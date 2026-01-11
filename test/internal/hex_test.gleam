import internal/hex.{InvalidHexChar, OddLength}

pub fn hex_to_bytes_lowercase_test() {
  assert hex.hex_to_bytes("48656c6c6f") == Ok(<<"Hello":utf8>>)
}

pub fn hex_to_bytes_uppercase_test() {
  assert hex.hex_to_bytes("48656C6C6F") == Ok(<<"Hello":utf8>>)
}

pub fn hex_to_bytes_empty_string_test() {
  assert hex.hex_to_bytes("") == Ok(<<>>)
}

pub fn hex_to_bytes_odd_length_test() {
  assert hex.hex_to_bytes("abc") == Error(OddLength)
}

pub fn hex_to_bytes_invalid_char_test() {
  assert hex.hex_to_bytes("abcg") == Error(InvalidHexChar("g", 3))
  assert hex.hex_to_bytes("xyz1") == Error(InvalidHexChar("x", 0))
  assert hex.hex_to_bytes("12!4") == Error(InvalidHexChar("!", 2))
}
