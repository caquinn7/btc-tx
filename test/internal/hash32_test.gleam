import internal/hash32.{InvalidByteCount}

pub fn from_bytes_le_returns_error_when_input_is_not_32_bytes_test() {
  assert Error(InvalidByteCount(0)) == hash32.from_bytes_le(<<>>)

  assert Error(InvalidByteCount(31))
    == hash32.from_bytes_le(<<
      1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0,
    >>)

  assert Error(InvalidByteCount(33))
    == hash32.from_bytes_le(<<
      1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
    >>)
}

pub fn from_bytes_le_returns_ok_when_input_is_32_bytes_test() {
  let assert Ok(_) =
    hash32.from_bytes_le(<<
      1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0,
    >>)
}
