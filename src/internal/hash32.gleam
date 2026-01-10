import gleam/bit_array

pub opaque type Hash32 {
  Hash32(bytes_le: BitArray)
}

pub type Hash32Error {
  InvalidByteCount(Int)
}

pub fn from_bytes_le(bytes: BitArray) -> Result(Hash32, Hash32Error) {
  case bytes {
    <<_:bytes-size(32)>> -> Ok(Hash32(bytes))
    _ -> Error(InvalidByteCount(bit_array.byte_size(bytes)))
  }
}
