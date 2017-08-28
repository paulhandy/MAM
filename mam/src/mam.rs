use curl::*;
use alloc::*;
use sign::iss;
use merkle;
use trytes::*;
use tmath::*;
//use auth::*;
use mask::*;
use errors::*;
use pascal;

const MAM_NONCE_LENGTH: usize = 81;

/// generate the message key for a root and an index.
/// It copies `root` to `key`, and adds `index` to it.
pub fn message_key(root: &[Trit], index: usize, key: &mut [Trit]) {
    assert!(root.len() >= HASH_LENGTH);
    assert!(key.len() >= HASH_LENGTH);
    key[..HASH_LENGTH].clone_from_slice(&root[..HASH_LENGTH]);
    add_assign(&mut key[..HASH_LENGTH], index as isize);
}

/// generates the address for a given mam `key`
/// for a mam, the key should consist of the merkle root and
/// an initialization vector, which is the index of the key  in the
/// merkle tree being used
pub fn message_id<T, C>(key: &mut [T], curl: &mut C)
where
    T: Copy + Clone + Sized,
    C: Curl<T>,
{
    curl.absorb(&key[..HASH_LENGTH]);
    key[..HASH_LENGTH].clone_from_slice(&curl.rate());
    curl.reset();
    curl.absorb(&key[..HASH_LENGTH]);
    key[..HASH_LENGTH].clone_from_slice(&curl.rate());
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
pub fn unmask_slice<C: Curl<Trit>>(out: &mut [Trit], key_chunk: &mut [Trit], curl: &mut C)
where
    C: Curl<Trit>,
{
    for chunk in out.chunks_mut(HASH_LENGTH) {
        let len = chunk.len();
        for i in 0..len {
            key_chunk[i] = trit_sum(chunk[i], -key_chunk[i]);
        }
        curl.absorb(chunk);
        chunk.clone_from_slice(&key_chunk[..len]);
        key_chunk.clone_from_slice(&curl.rate());
    }
}

pub fn compose<C, CB, H>(
    seed: &[Trit],
    message: &[Trit],
    addresses: &[Trit],
    next: &[Trit],
    out: &mut [Trit],
    start: isize,
    index: usize,
    security: u8,
    curl1: &mut C,
    curl2: &mut C,
    bcurl: &mut CB,
) -> Result<usize, MamError>
where
    C: Curl<Trit>,
    CB: Curl<BCTrit>,
    H: HammingNonce<Trit>,
{
    // get message length
    let message_len = message.len();
    // get the
    let message_length_trit_count = pascal::estimate(index as isize);
    let num_siblings = merkle::siblings_count(addresses.len() / HASH_LENGTH);
    let siblings_length_count = pascal::estimate(num_siblings as isize);
    let key_length = security as usize * iss::KEY_LENGTH;
    let signature_end = message_length_trit_count + HASH_LENGTH + message_len + MAM_NONCE_LENGTH +
        key_length;
    let siblings_start = signature_end + siblings_length_count;
    let siblings_end = siblings_start + num_siblings * HASH_LENGTH;
    let payload_end = siblings_end + HASH_LENGTH;
    if out.len() < payload_end {
        Err(MamError::ArrayOutOfBounds)
    } else {
        let mut cursor = 0;
        let mut key_chunk = [0 as Trit; HASH_LENGTH];
        merkle::siblings(
            addresses,
            index,
            &mut out[siblings_start..siblings_end],
            curl1,
        );
        out[siblings_end..siblings_end + HASH_LENGTH].clone_from_slice(&curl1.rate());

        // add the message length trits to the start of the message
        // mask it
        // append the next root
        // append the message
        // mask it
        {
            cursor = pascal::encode((message_len + HASH_LENGTH) as isize, out);
            message_key(
                &out[siblings_end..siblings_end + HASH_LENGTH],
                index,
                &mut key_chunk,
            );
            curl2.absorb(&key_chunk);
            key_chunk.clone_from_slice(curl2.rate());
            // copy pascal encoded message length to output
            let pascal_cursor = cursor;
            mask_slice(&mut out[..cursor], &mut key_chunk, curl2);
            // copy next root
            out[cursor..cursor + HASH_LENGTH].clone_from_slice(next);
            cursor += HASH_LENGTH;
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
            iss::subseed(
                seed,
                start + index as isize,
                &mut out[cursor..cursor + HASH_LENGTH],
                curl1,
            );
            curl1.reset();
            iss::key(&mut out[cursor..signature_end], security, curl1);
            curl1.reset();
            iss::signature(&key_chunk, &mut out[cursor..signature_end], curl1);
            pascal::encode(
                num_siblings as isize,
                &mut out[signature_end..siblings_length_count],
            );
            mask_slice(&mut out[cursor..siblings_end], &mut key_chunk, curl2);
            siblings_end
        };
        // return the end index of the masked payload
        Ok(cursor)
    }
}

pub enum PascalStatus {
    Negative,
    Positive,
    End,
}
pub fn parse<C>(
    payload: &[Trit],
    root: &[Trit],
    out: &mut [Trit],
    index: usize,
    curl1: &mut C,
    curl2: &mut C,
) -> Result<(Vec<Trit>, Vec<Trit>), MamError>
where
    C: Curl<Trit>,
{
    let mut key_chunk = [0 as Trit; HASH_LENGTH];
    let mut cursor = 0;
    let mut end = 0;
    let mut message_length = {
        let mut status: PascalStatus = PascalStatus::Negative;
        // Get pascal length
        for chunk in payload.chunks(HASH_LENGTH) {
            let mut j = 0;
            for tryte in chunk.chunks(3) {
                if num::trits2int(tryte) > 0 {
                    status = PascalStatus::Positive;
                }
                j += 3;
                if status == PascalStatus::Positive {
                    break;
                }
            }
            cursor = j;
            let len = match status {
                PascalStatus::Negative => chunk.len(),
                _ => j + 3 + 2 * (j / 3 + if (j / 3) % 3 == 0 { 0 } else { 1 }),
            };
            for i in 0..len {
                out[cursor + i] = trit_sum(chunk[i], -key_chunk[i]);
            }
            curl1.absorb(out[cursor..cursor + len]);
            key_chunk.clone_from_slice(&curl1.rate());
            if status == PascalStatus::End {
                break;
            }
        }
        pascal::decode(out[0..cursor]).0
    };
    {// Now, let's just copy the message into the out array, overwriting where we just were.
        out[..message_length].clone_from_slice(&payload[cursor
    }
    let mut index_trits = vec![0; num::min_trits(index as isize)];
    num::int2trits(index as isize, &mut index_trits);
    let channel_key: [&[Trit]; 2] = [&root, &index_trits];
    let mut unmasked_payload = payload.to_vec();
    unmask::<C>(&mut unmasked_payload, &channel_key, curl1);

    curl1.reset();
    //authenticate::<C>(&unmasked_payload, root, index, curl1, curl2)
    Err(MamError::ArrayOutOfBounds)
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
