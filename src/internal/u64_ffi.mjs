import { Result$Ok, Result$Error } from '../gleam.mjs';

export function u64LeToInt(bytes_le) {
  /*
  BitArray {
    bitSize: 64,
    byteSize: 8,
    bitOffset: 0,
    rawBuffer: Uint8Array(8) [
      255, 255, 255, 255,
      255, 255,  31,   0
    ]
  }
  */

  if (!bytes_le || bytes_le.byteSize !== 8) {
    return Result$Error(undefined);
  }

  const u8 = bytes_le.rawBuffer;
  if (!(u8 instanceof Uint8Array) || u8.length < 8) {
    return Result$Error(undefined);
  }

  const x = toBigInt(u8);

  if (x <= BigInt(Number.MAX_SAFE_INTEGER)) {
    return Result$Ok(Number(x));
  }

  return Result$Error(undefined);
}

export function u64LeToString(bytes_le) {
  if (!bytes_le || bytes_le.byteSize !== 8) {
    throw new Error('Expected 8-byte BitArray');
  }

  const u8 = bytes_le.rawBuffer;
  if (!(u8 instanceof Uint8Array) || u8.length < 8) {
    throw new Error('Invalid BitArray buffer');
  }

  const x = toBigInt(u8);
  return x.toString(10);
}

function toBigInt(u8) {
  let x = 0n;
  for (let i = 0; i < 8; i++) {
    x |= BigInt(u8[i]) << (8n * BigInt(i));
  }
  return x;
}

