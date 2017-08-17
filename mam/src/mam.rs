use curl::*;
use alloc::*;
use sign::iss;
use merkle;
use pascal;
use trytes::*;
use tmath::*;
use auth::*;
use mask::*;
use errors::*;

const MAM_NONCE_LENGTH: usize = 81;

pub fn message_id<T, C>(keys: &[Vec<T>], index: usize, curl: &mut C) -> Vec<T>
where
    T: Copy + Clone + Sized,
    C: Curl<T>,
{
    for key in keys {
        curl.absorb(key.as_slice());
    }
    let mask = curl.rate().to_vec();
    curl.reset();
    curl.absorb(&mask);
    curl.rate().to_vec()
}

pub fn mask_slice<C: Curl<Trit>>(out: &mut [Trit], key_chunk: &mut [Trit], curl: &mut C)
where
    C: Curl<Trit>,
{
    for chunk in out.chunks_mut(HASH_LENGTH) {
        let len = chunk.len();
        for i in 0..len {
            key_chunk[i] = trit_sum(chunk[i], key_chunk[i]);
        }
        curl.absorb(chunk);
        chunk.clone_from_slice(&key_chunk[..len]);
        key_chunk.clone_from_slice(&curl.rate());
    }
}

pub fn create<C, CB, H>(
    seed: &[Trit],
    message: &[Trit],
    addresses: &[Trit],
    next: &[Trit],
    out: &mut [Trit],
    index: usize,
    security: u8,
    curl1: &mut C,
    curl2: &mut C,
    bcurl: &mut CB,
) -> usize
where
    C: Curl<Trit>,
    CB: Curl<BCTrit>,
    H: HammingNonce<Trit>,
{
    let key_length = security as usize * iss::KEY_LENGTH;
    let mut cursor = 0;
    let mut key_chunk = [0 as Trit; HASH_LENGTH];
    merkle::siblings(addresses, out[siblings_start..siblings_end], index, curl1);

    // add the message length trits to the start of the message
    // mask it
    // append the next root
    // append the message
    // mask it
    {
        curl2.absorb(&curl1.rate());
        num::int2trits(index as isize, out);
        curl2.absorb(&out[..num::min_trits(index as isize)]);
        curl2.squeeze(&mut key_chunk);
        // copy pascal encoded message length to output
        let message_len = message.len();
        cursor = pascal::encode(message_len + HASH_LENGTH, out);
        let pascal_cursor = cursor;
        mask_slice(&mut out[..cursor], &mut key_chunk, curl2);
        // copy next root
        cursor += HASH_LENGTH;
        out[pascal_cursor..cursor].clone_from_slice(next);
        // copy message trits to output
        out[cursor..cursor + message_len].clone_from_slice(message);
        cursor += message_len;
        // mask the
        mask_slice(&mut out[pascal_cursor..cursor], &mut key_chunk, curl2);
    }
    // get the authenticated cipher nonce
    // and mask it
    cursor = {
        curl1.state_mut().clone_from_slice(curl2.state());
        let nonce_len = H::search(security, 0, MAM_NONCE_LENGTH, curl1, bcurl).unwrap();
        let nonce_end = cursor + nonce_len;
        out[cursor..nonce_end].clone_from_slice(&curl1.rate()[..nonce_len]);
        mask_slice(&mut out[cursor..nonce_end], &mut key_chunk, curl2);
        nonce_end
    };
    // sign, add siblings,
    // and mask
    cursor = {
        let signature_end = cursor + key_length;
        curl1.reset();
        iss::subseed(seed, index, &mut out[cursor..cursor + HASH_LENGTH], curl1);
        curl1.reset();
        iss::key(&mut out[cursor..signature_end], security, curl1);
        curl1.reset();
        iss::signature(&key_chunk, &mut out[cursor..signature_end], curl1);
        let siblings_end = signature_end + addresses.len();
        out[signature_end..siblings_end].clone_from_slice(siblings);
        mask_slice(&mut out[cursor..siblings_end], &mut key_chunk, curl2);
        siblings_end
    };
    curl1.reset();
    curl2.reset();
    bcurl.reset();
    // return the end index of the masked payload
    cursor
}

// returns message_length
pub fn parse<C>(
    payload: &mut [Trit],
    root: &[Trit],
    index: usize,
    curl1: &mut C,
    curl2: &mut C,
) -> Result<usize, MamError>
where
    C: Curl<Trit>,
{
    let mut index_trits = vec![0; num::min_trits(index as isize)];
    num::int2trits(index as isize, &mut index_trits);
    let channel_key: [&[Trit]; 2] = [&root, &index_trits];
    let mut unmasked_payload = payload.to_vec();
    unmask::<C>(&mut unmasked_payload, &channel_key, curl1);

    curl1.reset();
    authenticate::<C>(&unmasked_payload, root, index, curl1, curl2)
}

#[cfg(test)]
mod tests {
    use super::*;
    use curl_cpu::*;
    use alloc::Vec;
    #[test]
    fn it_works() {
        let seed: Vec<Trit> = "ABCDEFGHIJKLMNOPQRSTUVWXYZ9\
                             ABCDEFGHIJKLMNOPQRSTUVWXYZ9\
                             ABCDEFGHIJKLMNOPQRSTUVWXYZ9"
            .chars()
            .flat_map(char_to_trits)
            .cloned()
            .collect();
        let message: Vec<Trit> = "IAMSOMEMESSAGE9HEARMEROARMYMESSAGETOTHEWORLDYOUHEATHEN"
            .chars()
            .flat_map(char_to_trits)
            .cloned()
            .collect();
        let security = 1;
        let start = 1;
        let count = 9;
        let next_start = start + count;
        let next_count = 4;
        let index = 3;

        let mut c1 = CpuCurl::<Trit>::default();
        let mut c2 = CpuCurl::<Trit>::default();
        let mut bc = CpuCurl::<BCTrit>::default();

        let (masked_payload, root) = create::<CpuCurl<Trit>, CpuCurl<BCTrit>, CpuHam>(
            &seed,
            &message,
            start,
            count,
            index,
            next_start,
            next_count,
            security,
            &mut c1,
            &mut c2,
            &mut bc,
        );
        c1.reset();
        c2.reset();

        let result = parse::<CpuCurl<Trit>>(&masked_payload, &root, index, &mut c1, &mut c2)
            .ok()
            .unwrap();
        assert_eq!(result.0, message);
    }
}
