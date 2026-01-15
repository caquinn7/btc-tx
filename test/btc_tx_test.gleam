import btc_tx.{CompactSizeError, InvalidValueRange, ParseFailed, ReaderError}
import gleam/option.{Some}
import gleeunit
import internal/compact_size
import internal/reader

const legacy_v1_tx = "0100000001098ebbff18cf40ad3ba02ded7d3558d7ca6ee96c990c8fdfb99cf61d88ad2c680100000000ffffffff01f0a29a3b000000001976a914012e2ba6a051c033b03d712ca2ea00a35eac1e7988ac00000000"

const segwit_v1_tx = "01000000000101db6b1b20aa0fd7b23880be2ecbd4a98130974cf4748fb66092ac4d3ceb1a5477010000001716001479091972186c449eb1ded22b78e40d009bdf0089feffffff02b8b4eb0b000000001976a914a457b684d7f0d539a46a45bbc043f35b59d0d96388ac0008af2f000000001976a914fd270b1ee6abcaea97fea7ad0402e8bd8ad6d77c88ac02473044022047ac8e878352d3ebbde1c94ce3a10d057c24175747116f8288e5d794d12d482f0220217f36a485cae903c713331d877c1f64677e3622ad4010726870540656fe9dcb012103ad1d8e89212f0b92c74d23bb710c00662ad1470198ac48c43f7d6f93a2a2687392040000"

const legacy_v2_tx = "02000000019945a5a440f2d3712ff095cb1efefada1cc52e139defedb92a313daed49d5678010000006a473044022031b6a6b79c666d5568a9ac7c116cacf277e11521aebc6794e2b415ef8c87c899022001fe272499ea32e6e1f6e45eb656973fbb55252f7acc64e1e1ac70837d5b7d9f0121023dec241e4851d1ec1513a48800552bae7be155c6542629636bcaa672eee971dcffffffff01a70200000000000017a9148ce773d254dc5df886b95848880e0b40f10564328700000000"

pub fn main() -> Nil {
  gleeunit.main()
}

pub fn decode_legacy_full_tx_sets_version_and_is_segwit_false_test() {
  let assert Ok(result) = btc_tx.decode_hex(legacy_v1_tx)

  assert btc_tx.get_version(result) == 1
  assert !btc_tx.is_segwit(result)
}

pub fn decode_segwit_full_tx_sets_version_and_is_segwit_true_test() {
  let assert Ok(result) = btc_tx.decode_hex(segwit_v1_tx)

  assert btc_tx.get_version(result) == 1
  assert btc_tx.is_segwit(result)
}

pub fn decode_legacy_v2_parses_version_2_test() {
  let assert Ok(result) = btc_tx.decode_hex(legacy_v2_tx)

  assert btc_tx.get_version(result) == 2
  assert !btc_tx.is_segwit(result)
}

pub fn decode_errors_when_input_shorter_than_4_bytes_test() {
  let assert Error(ParseFailed(parse_err)) = btc_tx.decode_hex("010203")

  assert btc_tx.parse_error_offset(parse_err) == 0

  assert btc_tx.parse_error_kind(parse_err)
    == ReaderError(reader.UnexpectedEof(4, 3))
}

pub fn decode_does_not_misclassify_segwit_when_discriminator_is_missing_test() {
  let version = <<1:little-size(32)>>

  let assert Error(ParseFailed(parse_err)) = btc_tx.decode(version)

  assert btc_tx.parse_error_offset(parse_err) == 4

  assert btc_tx.parse_error_kind(parse_err)
    == CompactSizeError(compact_size.ReaderError(reader.UnexpectedEof(1, 0)))
}

pub fn decode_does_not_misclassify_segwit_when_discriminator_is_truncated_test() {
  let version = <<1:little-size(32)>>
  let marker = <<0:size(8)>>

  let assert Error(ParseFailed(parse_err)) =
    btc_tx.decode(<<version:bits, marker:bits>>)

  assert btc_tx.parse_error_offset(parse_err) == 5

  assert btc_tx.parse_error_kind(parse_err)
    == InvalidValueRange("vin_count", "0", Some(1), Some(0))
}

pub fn decode_does_not_misclassify_segwit_when_flag_is_not_01_test() {
  let version = <<1:little-size(32)>>
  let marker = <<0:size(8)>>
  let flag = <<2:little-size(8)>>

  let assert Error(ParseFailed(parse_err)) =
    btc_tx.decode(<<version:bits, marker:bits, flag:bits>>)

  assert btc_tx.parse_error_offset(parse_err) == 5

  assert btc_tx.parse_error_kind(parse_err)
    == InvalidValueRange("vin_count", "0", Some(1), Some(0))
}
