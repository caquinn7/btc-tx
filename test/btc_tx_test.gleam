import btc_tx.{
  CompactSizeError, DecodePolicy, InsufficientBytesForInputs, InvalidValueRange,
  ParseFailed, ReaderError,
}
import gleam/option.{Some}
import gleeunit
import internal/compact_size
import internal/reader

const legacy_v1_tx = "0100000001098ebbff18cf40ad3ba02ded7d3558d7ca6ee96c990c8fdfb99cf61d88ad2c680100000000ffffffff01f0a29a3b000000001976a914012e2ba6a051c033b03d712ca2ea00a35eac1e7988ac00000000"

const segwit_v1_tx = "01000000000101db6b1b20aa0fd7b23880be2ecbd4a98130974cf4748fb66092ac4d3ceb1a5477010000001716001479091972186c449eb1ded22b78e40d009bdf0089feffffff02b8b4eb0b000000001976a914a457b684d7f0d539a46a45bbc043f35b59d0d96388ac0008af2f000000001976a914fd270b1ee6abcaea97fea7ad0402e8bd8ad6d77c88ac02473044022047ac8e878352d3ebbde1c94ce3a10d057c24175747116f8288e5d794d12d482f0220217f36a485cae903c713331d877c1f64677e3622ad4010726870540656fe9dcb012103ad1d8e89212f0b92c74d23bb710c00662ad1470198ac48c43f7d6f93a2a2687392040000"

const legacy_v2_tx = "02000000019945a5a440f2d3712ff095cb1efefada1cc52e139defedb92a313daed49d5678010000006a473044022031b6a6b79c666d5568a9ac7c116cacf277e11521aebc6794e2b415ef8c87c899022001fe272499ea32e6e1f6e45eb656973fbb55252f7acc64e1e1ac70837d5b7d9f0121023dec241e4851d1ec1513a48800552bae7be155c6542629636bcaa672eee971dcffffffff01a70200000000000017a9148ce773d254dc5df886b95848880e0b40f10564328700000000"

const version1 = <<1:little-size(32)>>

const min_txin_size_bytes = 41

pub fn main() -> Nil {
  gleeunit.main()
}

// version and segwit

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
  let assert Error(ParseFailed(parse_err)) = btc_tx.decode(version1)

  assert btc_tx.parse_error_offset(parse_err) == 4

  assert btc_tx.parse_error_kind(parse_err)
    == CompactSizeError(compact_size.ReaderError(reader.UnexpectedEof(1, 0)))
}

pub fn decode_does_not_misclassify_segwit_when_discriminator_is_truncated_test() {
  let marker = <<0:size(8)>>

  let assert Error(ParseFailed(parse_err)) =
    btc_tx.decode(<<version1:bits, marker:bits>>)

  assert btc_tx.parse_error_offset(parse_err) == 5

  assert btc_tx.parse_error_kind(parse_err)
    == InsufficientBytesForInputs(
      remaining: 0,
      min_txin_size: min_txin_size_bytes,
    )
}

pub fn decode_does_not_misclassify_segwit_when_flag_is_not_01_test() {
  let marker = <<0:size(8)>>
  let flag = <<2:little-size(8)>>

  let assert Error(ParseFailed(parse_err)) =
    btc_tx.decode(<<version1:bits, marker:bits, flag:bits>>)

  assert btc_tx.parse_error_offset(parse_err) == 5

  assert btc_tx.parse_error_kind(parse_err)
    == InsufficientBytesForInputs(
      remaining: 1,
      min_txin_size: min_txin_size_bytes,
    )
}

// vin_count parsing and validation

pub fn decode_returns_invalid_value_range_when_vin_count_zero_test() {
  // Construct: version (4 bytes) + vin_count (CompactSize = 0x00) + 41 bytes
  // of padding so that `remaining >= min_txin_size` and the validator
  // produces an InvalidValueRange for vin_count == 0.

  let vin_count = 0
  let input_padding = <<0:little-size({ 1 * min_txin_size_bytes * 8 })>>

  let assert Error(ParseFailed(parse_err)) =
    btc_tx.decode(<<version1:bits, vin_count:size(8), input_padding:bits>>)

  assert btc_tx.parse_error_offset(parse_err) == 5

  assert btc_tx.parse_error_kind(parse_err)
    == InvalidValueRange("vin_count", vin_count, Some(1), Some(1))
}

pub fn validate_vin_count_minimum_succeeds_test() {
  // version (4 bytes) + vin_count (CompactSize = 0x01) + 41 bytes padding

  let vin_count = 1
  let input_padding = <<0:little-size({ 1 * min_txin_size_bytes * 8 })>>

  let assert Ok(_) =
    btc_tx.decode(<<version1:bits, vin_count:size(8), input_padding:bits>>)
}

pub fn validate_vin_count_within_limits_succeeds_test() {
  // version (4 bytes) + vin_count (CompactSize = 0x02) + padding for >= 2 inputs
  // padding: 2 * 41 = 82 bytes -> 82 * 8 = 656 bits
  // enforce a policy that permits at least 2 inputs

  let vin_count = 2
  let input_padding = <<0:little-size({ 2 * min_txin_size_bytes * 8 })>>

  let assert Ok(_) =
    btc_tx.decode_with_policy(
      <<version1:bits, vin_count:size(8), input_padding:bits>>,
      DecodePolicy(max_vin_count: 10),
    )
}

pub fn validate_vin_count_equals_policy_succeeds_test() {
  // Pick a small policy (3). Create vin_count == 3 and supply >= 3 * 41 bytes padding
  // so that max_inputs_by_bytes >= policy and the policy is the active cap.
  // should succeed when enforcing a policy that allows exactly 3 inputs

  let vin_count = 3
  let input_padding = <<0:little-size({ 3 * min_txin_size_bytes * 8 })>>

  let assert Ok(_) =
    btc_tx.decode_with_policy(
      <<version1:bits, vin_count:size(8), input_padding:bits>>,
      DecodePolicy(max_vin_count: 3),
    )
}

pub fn validate_vin_count_exceeds_policy_error_test() {
  // Use a small policy (2). Set vin_count == 3 and provide padding for
  // exactly 2 inputs (2 * 41 = 82 bytes) so max_inputs_by_bytes == 2 and
  // the policy cap is active. Validator should reject vin_count == 3.

  let vin_count = 3
  let input_padding = <<0:little-size({ 2 * min_txin_size_bytes * 8 })>>

  let assert Error(ParseFailed(parse_err)) =
    btc_tx.decode_with_policy(
      <<version1:bits, vin_count:size(8), input_padding:bits>>,
      DecodePolicy(max_vin_count: 2),
    )

  assert btc_tx.parse_error_offset(parse_err) == 5

  assert btc_tx.parse_error_kind(parse_err)
    == InvalidValueRange("vin_count", vin_count, Some(1), Some(2))
}

pub fn validate_vin_count_exceeds_structural_error_test() {
  // Provide padding for exactly 2 inputs (2 * 41 = 82 bytes) so
  // max_inputs_by_bytes == 2. Use a large policy so the structural
  // limit is the active cap, then assert vin_count == 3 is rejected.

  let vin_count = 3
  let input_padding = <<0:little-size({ 2 * min_txin_size_bytes * 8 })>>

  let assert Error(ParseFailed(parse_err)) =
    btc_tx.decode_with_policy(
      <<version1:bits, vin_count:size(8), input_padding:bits>>,
      DecodePolicy(max_vin_count: 100),
    )

  assert btc_tx.parse_error_offset(parse_err) == 5

  assert btc_tx.parse_error_kind(parse_err)
    == InvalidValueRange("vin_count", vin_count, Some(1), Some(2))
}

pub fn validate_vin_count_structural_boundary_succeeds_test() {
  // Provide padding for exactly 2 inputs (2 * 41 = 82 bytes) so
  // max_inputs_by_bytes == 2. Use a large policy so the structural
  // limit is the active cap, then assert vin_count == 2 succeeds.

  let vin_count = 2
  let input_padding = <<0:little-size({ vin_count * min_txin_size_bytes * 8 })>>

  let assert Ok(_) =
    btc_tx.decode_with_policy(
      <<version1:bits, vin_count:size(8), input_padding:bits>>,
      DecodePolicy(max_vin_count: 100),
    )
}

pub fn validate_vin_count_policy_wins_over_structural_test() {
  // Provide padding for 11 inputs (11 * 41 = 451 bytes) so
  // max_inputs_by_bytes == 11. Use a small policy (10) so the policy
  // limit is lower than structural, then assert vin_count == 11 is rejected
  // with max = policy (10).

  let vin_count = 11
  let input_padding = <<0:little-size({ vin_count * min_txin_size_bytes * 8 })>>

  let assert Error(ParseFailed(parse_err)) =
    btc_tx.decode_with_policy(
      <<version1:bits, vin_count:size(8), input_padding:bits>>,
      DecodePolicy(max_vin_count: 10),
    )

  assert btc_tx.parse_error_offset(parse_err) == 5

  assert btc_tx.parse_error_kind(parse_err)
    == InvalidValueRange("vin_count", vin_count, Some(1), Some(10))
}

// Two runtime-specific tests below. On JavaScript, `u64.to_int` fails for
// values greater than `Number.MAX_SAFE_INTEGER`, producing
// `IntegerOutOfRange(...)`. On Erlang, `u64.to_int` succeeds and the
// validator reports `InvalidValueRange(...)` for excessively large counts.

@target(javascript)
pub fn validate_vin_count_uint_conversion_failure_js_test() {
  // CompactSize 0xFF with max u64 (18446744073709551615), which exceeds
  // JavaScript's MAX_SAFE_INTEGER and will fail u64.to_int conversion.

  let compact_prefix = <<255:size(8)>>
  let u64_max = <<
    255:size(8),
    255:size(8),
    255:size(8),
    255:size(8),
    255:size(8),
    255:size(8),
    255:size(8),
    255:size(8),
  >>
  let vin_count = <<compact_prefix:bits, u64_max:bits>>
  // padding: 41 bytes so remaining >= min_txin_size.
  let padding = <<0:little-size({ min_txin_size_bytes * 8 })>>

  let assert Error(ParseFailed(parse_err)) =
    btc_tx.decode(<<
      version1:bits,
      vin_count:bits,
      padding:bits,
    >>)

  assert btc_tx.parse_error_offset(parse_err) == 13

  assert btc_tx.parse_error_kind(parse_err)
    == btc_tx.IntegerOutOfRange("18446744073709551615")
}

@target(erlang)
pub fn validate_vin_count_large_value_invalid_range_erlang_test() {
  // CompactSize 0xFF with max u64 (18446744073709551615). On Erlang,
  // conversion to `Int` succeeds (arbitrary precision), so the validator
  // returns InvalidValueRange because the value vastly exceeds max_inputs.

  let compact_prefix = <<255:size(8)>>
  let u64_max = <<
    255:size(8),
    255:size(8),
    255:size(8),
    255:size(8),
    255:size(8),
    255:size(8),
    255:size(8),
    255:size(8),
  >>
  let vin_count = <<compact_prefix:bits, u64_max:bits>>
  // padding: 41 bytes so remaining >= min_txin_size.
  let padding = <<0:little-size({ min_txin_size_bytes * 8 })>>

  let assert Error(ParseFailed(parse_err)) =
    btc_tx.decode(<<
      version1:bits,
      vin_count:bits,
      padding:bits,
    >>)

  assert btc_tx.parse_error_offset(parse_err) == 13

  assert btc_tx.parse_error_kind(parse_err)
    == btc_tx.InvalidValueRange(
      "vin_count",
      18_446_744_073_709_551_615,
      Some(1),
      Some(1),
    )
}

pub fn validate_vin_count_insufficient_bytes_for_inputs_test() {
  // Construct: version (4 bytes) + vin_count (CompactSize = 0x01) + 40 bytes
  // of padding so that `remaining < min_txin_size` and the validator
  // produces an InsufficientBytesForInputs error.

  let vin_count = 1
  let input_padding = <<0:little-size({ 1 * { min_txin_size_bytes - 1 } * 8 })>>

  let assert Error(ParseFailed(parse_err)) =
    btc_tx.decode(<<version1:bits, vin_count:size(8), input_padding:bits>>)

  assert btc_tx.parse_error_offset(parse_err) == 5

  assert btc_tx.parse_error_kind(parse_err)
    == InsufficientBytesForInputs(
      remaining: min_txin_size_bytes - 1,
      min_txin_size: min_txin_size_bytes,
    )
}
