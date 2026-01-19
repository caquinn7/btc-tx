//// btc_tx provides facilities for parsing and modeling Bitcoin transaction data
//// in a form suitable for inspection, analysis, and reference.

import gleam/bool
import gleam/int
import gleam/list
import gleam/option.{type Option, Some}
import gleam/result
import internal/compact_size
import internal/hash32.{type Hash32}
import internal/hex
import internal/reader.{type Reader}
import internal/u64.{type U64}

// ---- Transaction types ----

/// A Bitcoin transaction.
///
/// A transaction transfers value by consuming previously created outputs
/// (inputs) and creating new outputs. Transactions are either legacy
/// (pre-SegWit) or SegWit, which affects how witness data is serialized
/// and how transaction identifiers are computed.
pub opaque type Transaction {
  /// A legacy (non-SegWit) transaction.
  ///
  /// Legacy transactions do not include witness data and compute their
  /// transaction identifier (txid) from the full serialization.
  Legacy(
    /// The transaction version number.
    /// 
    /// Unknown or future version values are permitted by Bitcoin consensus
    /// rules and are therefore not rejected by the decoder.
    version: Int,
    /// The list of transaction inputs.
    inputs: List(TxIn(Nil)),
    /// The list of transaction outputs.
    outputs: List(TxOut),
    /// The transaction lock time.
    lock_time: Int,
  )

  /// A SegWit transaction.
  ///
  /// SegWit transactions separate witness data from the main transaction
  /// serialization and compute both a txid (non-witness data) and a wtxid
  /// (full serialization including witness data).
  Segwit(
    /// The transaction version number.
    /// 
    /// Unknown or future version values are permitted by Bitcoin consensus
    /// rules and are therefore not rejected by the decoder.
    version: Int,
    /// The list of transaction inputs, each with associated witness data.
    inputs: List(TxIn(List(WitnessItem))),
    /// The list of transaction outputs.
    outputs: List(TxOut),
    /// The transaction lock time.
    lock_time: Int,
  )
}

/// A transaction input.
///
/// An input references a previous transaction output and provides the data
/// required to satisfy that output’s spending conditions.
pub opaque type TxIn(witness) {
  TxIn(
    /// The previous output being spent, or a coinbase marker.
    prev_out: PrevOut,
    /// The unlocking script (scriptSig) for this input.
    ///
    /// This script is evaluated together with the referenced output’s
    /// scriptPubKey during script execution.
    script_sig: ScriptBytes,
    /// The sequence number associated with this input.
    ///
    /// Sequence numbers are used for relative lock-time semantics and
    /// transaction replacement rules.
    sequence: Int,
    /// Witness data associated with this input.
    ///
    /// For legacy transactions this is `Nil`; for SegWit transactions this
    /// is a list of witness stack items.
    witness: witness,
  )
}

/// A reference to a previous transaction output.
///
/// This identifies the output being consumed by a transaction input.
pub opaque type PrevOut {
  /// A special marker used by coinbase transactions.
  ///
  /// Coinbase inputs do not reference a previous transaction output.
  Coinbase

  /// A reference to a specific output of a previous transaction.
  ///
  /// `txid` identifies the transaction, and `vout` is the zero-based index
  /// of the output within that transaction.
  OutPoint(txid: TxId, vout: Int)
}

/// Raw Bitcoin script bytes.
///
/// This type represents an uninterpreted script as it appears on the wire.
/// No validation or opcode parsing is performed at this level.
pub opaque type ScriptBytes {
  ScriptBytes(bytes: BitArray)
}

/// A single witness stack item.
///
/// Witness items are arbitrary byte sequences provided as part of SegWit
/// transaction inputs and are interpreted by script evaluation rules.
pub opaque type WitnessItem {
  WitnessItem(bytes: BitArray)
}

/// A transaction output.
///
/// An output assigns a value and specifies the conditions under which that
/// value may be spent in the future.
pub opaque type TxOut {
  TxOut(
    /// The number of satoshis assigned to this output.
    value: Satoshis,
    /// The locking script (scriptPubKey) defining the spending conditions.
    script_pubkey: ScriptBytes,
  )
}

/// A quantity of satoshis. (1 Bitcoin = 100,000,000 Satoshis)
///
/// A satoshi is the smallest unit of Bitcoin.
/// Valid values are non-negative and bounded by the consensus maximum money supply.
pub opaque type Satoshis {
  Satoshis(Int)
}

/// The transaction identifier (txid).
///
/// This is the double SHA-256 hash of the transaction’s
/// non-witness serialization and is distinct from the wtxid.
pub opaque type TxId {
  TxId(Hash32)
}

/// The witness transaction identifier (wtxid).
///
/// This is the double SHA-256 hash of the transaction’s
/// full serialization, including witness data.
pub opaque type WtxId {
  WtxId(Hash32)
}

pub fn get_version(tx: Transaction) -> Int {
  tx.version
}

pub fn is_segwit(tx: Transaction) -> Bool {
  case tx {
    Legacy(..) -> False
    Segwit(..) -> True
  }
}

// ---- Error handling ----

/// An error that occurred while decoding a Bitcoin transaction.
///
/// This error type distinguishes between failures that occur during hex-to-bytes
/// conversion and failures that occur during transaction parsing.
pub type DecodeError {
  /// The hexadecimal string could not be converted to bytes.
  ///
  /// This occurs before any transaction parsing begins, typically due to an
  /// odd-length hex string or the presence of invalid hexadecimal characters.
  HexToBytesFailed(hex.HexToBytesError)

  /// The byte sequence could not be parsed as a Bitcoin transaction.
  ///
  /// This wraps a `ParseError` containing details about what went wrong during
  /// the transaction parsing phase.
  ParseFailed(ParseError)
}

/// An error that occurred while parsing a Bitcoin transaction.
///
/// This opaque type contains details about what went wrong during parsing,
/// including the byte offset where the error occurred, the kind of error,
/// and the parsing context (which fields or structures were being parsed).
pub opaque type ParseError {
  ParseError(offset: Int, kind: ParseErrorKind, ctx: List(ParseContext))
}

/// The specific kind of error that occurred during parsing.
///
/// This type categorizes parsing failures into distinct categories, ranging from
/// low-level binary reading errors to semantic constraint violations.
pub type ParseErrorKind {
  /// A low-level binary reader operation failed.
  ///
  /// This error wraps failures from the underlying `Reader`, such as attempting
  /// to read beyond the end of the input or requesting an invalid number of bytes.
  ReaderError(reader.ReaderError)

  /// A CompactSize-encoded integer could not be parsed.
  ///
  /// This error wraps failures from CompactSize decoding operations, such as
  /// encountering an unexpected end of input or detecting a non-minimal encoding
  /// that violates Bitcoin's canonical serialization rules.
  CompactSizeError(compact_size.CompactSizeError)

  /// The remaining bytes are insufficient to encode even one transaction input.
  ///
  /// At least `min_txin_size` bytes are required to encode a single transaction
  /// input, but only `remaining` bytes were available. This indicates that the
  /// transaction is truncated or structurally invalid, and no positive `vin_count`
  /// can be satisfied.
  InsufficientBytesForInputs(remaining: Int, min_txin_size: Int)

  /// A decoded integer value exceeds the range representable by the runtime.
  ///
  /// This typically occurs when converting a 64-bit unsigned value to a host
  /// integer type. The original value is preserved as a string for diagnostics.
  IntegerOutOfRange(String)

  /// A decoded numeric value fell outside the allowed range for the given field.
  ///
  /// The value was successfully decoded from well-formed input, but is rejected
  /// because it violates constraints implied by the field’s meaning or by
  /// parser-defined limits (for example, unreasonable counts or lengths, invalid flag values,
  /// or values outside an expected range for the field), even when the serialized data itself is valid.
  ///
  /// `field` identifies the logical field being validated, `value` is the decoded
  /// value, and `min` / `max` define the permitted inclusive range.
  InvalidValueRange(
    field: String,
    value: Int,
    min: Option(Int),
    max: Option(Int),
  )

  /// A catch-all error for unexpected or internal parsing failures that do not
  /// fit any of the structured error categories.
  ///
  /// This should be used sparingly and primarily for truly exceptional cases.
  Other(message: String)
}

/// Contextual information about where in the transaction structure a parsing error occurred.
pub type ParseContext {
  /// The error occurred while parsing the top-level transaction structure.
  ///
  /// This is typically added once at the outermost decode layer.
  Tx

  /// The error occurred while parsing the transaction’s input vector
  /// (the `vin` field).
  Inputs

  /// The error occurred while parsing a specific input within the input vector.
  ///
  /// The wrapped `Int` is the zero-based index of the input being parsed.
  Input(Int)

  /// The error occurred while parsing the transaction’s output vector
  /// (the `vout` field).
  Outputs

  /// The error occurred while parsing a specific output within the output vector.
  ///
  /// The wrapped `Int` is the zero-based index of the output being parsed.
  Output(Int)

  /// The error occurred while parsing witness data for a specific input.
  ///
  /// The wrapped `Int` is the zero-based index of the input whose witness
  /// stack was being parsed.
  Witness(Int)

  /// The error occurred while parsing or validating a specific logical field.
  ///
  /// This is typically used to label reads of fixed-size or length-prefixed
  /// fields such as `"version"`, `"sequence"`, `"lock_time"`, `"script_sig"`,
  /// or `"script_pubkey"`.
  Field(String)
}

pub fn parse_error_offset(err: ParseError) -> Int {
  err.offset
}

pub fn parse_error_kind(err: ParseError) -> ParseErrorKind {
  err.kind
}

pub fn parse_error_ctx(err: ParseError) -> List(ParseContext) {
  err.ctx
}

fn new_parse_error(kind: ParseErrorKind, reader: Reader) -> ParseError {
  ParseError(reader.get_offset(reader), kind:, ctx: [])
}

fn with_contexts(err: ParseError, ctx: List(ParseContext)) -> ParseError {
  list.fold(ctx, err, fn(err, ctx) { ParseError(..err, ctx: [ctx, ..err.ctx]) })
}

// ---- Context-threading parser combinators ----

/// A parsing computation that threads both the `Reader` and `ParseContext`.
///
/// This allows us to use Gleam's `use` syntax to elegantly compose parsing
/// operations while automatically managing context propagation.
type Parser(a) =
  fn(Reader, List(ParseContext)) -> Result(#(Reader, a), DecodeError)

// -- Combinators: functions that combine or transform parsers

/// Run a Parser computation with an initial reader and context.
/// 
/// Combinator: chains parsers together using `use` syntax.
fn run_parse(
  reader: Reader,
  ctx: List(ParseContext),
  parser: Parser(a),
  next: fn(Reader, a) -> Result(b, DecodeError),
) -> Result(b, DecodeError) {
  use #(reader, value) <- result.try(parser(reader, ctx))
  next(reader, value)
}

/// Add a context layer to a parsing computation.
///
/// Combinator: wraps a Parser to prepend context to its context list.
fn in_context(ctx: ParseContext, parser: Parser(a)) -> Parser(a) {
  fn(reader, outer_ctx) { parser(reader, [ctx, ..outer_ctx]) }
}

// -- Parsers: functions that create parsers for specific data types

/// Lift a reader operation into a Parser, adding error mapping.
fn read_field(
  read_fn: fn(Reader) -> Result(#(Reader, a), reader.ReaderError),
) -> Parser(a) {
  fn(reader, ctx) {
    reader
    |> read_fn
    |> result.map_error(fn(err) {
      err
      |> ReaderError
      |> new_parse_error(reader)
      |> with_contexts(ctx)
      |> ParseFailed
    })
  }
}

/// Lift a compact_size read into a Parser, adding error mapping.
fn read_compact_size() -> Parser(U64) {
  fn(reader, ctx) {
    reader
    |> compact_size.read
    |> result.map_error(fn(err) {
      err
      |> CompactSizeError
      |> new_parse_error(reader)
      |> with_contexts(ctx)
      |> ParseFailed
    })
  }
}

// ---- Decoding functions ----

pub type DecodePolicy {
  DecodePolicy(max_vin_count: Int)
}

pub fn decode(bytes: BitArray) -> Result(Transaction, DecodeError) {
  decode_with_policy(bytes, DecodePolicy(max_vin_count: 100_000))
}

pub fn decode_with_policy(
  bytes: BitArray,
  policy: DecodePolicy,
) -> Result(Transaction, DecodeError) {
  let reader = reader.new(bytes)
  let tx_ctx = [Tx]

  use reader, version <- run_parse(
    reader,
    tx_ctx,
    in_context(Field("version"), read_field(reader.read_i32_le)),
  )

  use reader, is_segwit <- run_parse(reader, tx_ctx, detect_segwit())

  use reader, vin_count_u64 <- run_parse(
    reader,
    tx_ctx,
    in_context(Inputs, in_context(Field("vin_count"), read_compact_size())),
  )

  use reader, vin_count <- run_parse(
    reader,
    [Inputs, ..tx_ctx],
    validate_vin_count(vin_count_u64, policy.max_vin_count),
  )

  Ok(case is_segwit {
    True -> Segwit(version:, inputs: [], outputs: [], lock_time: 0)
    False -> Legacy(version:, inputs: [], outputs: [], lock_time: 0)
  })
}

pub fn decode_hex(hex: String) -> Result(Transaction, DecodeError) {
  case hex.hex_to_bytes(hex) {
    Ok(bytes) -> decode(bytes)
    Error(err) -> Error(HexToBytesFailed(err))
  }
}

/// Detect whether this is a SegWit transaction by peeking at the marker/flag bytes.
///
/// Returns `True` if SegWit marker (0x00, 0x01) is present,`False` otherwise.
/// Side effect: consumes the marker/flag bytes if SegWit is detected.
fn detect_segwit() -> Parser(Bool) {
  fn(reader, ctx) {
    use reader, is_segwit <- run_parse(reader, ctx, peek_segwit())

    let reader = case is_segwit {
      True -> {
        // safe to assert because we already peeked the next two bytes
        let assert Ok(reader) = reader.skip_bytes(reader, 2)
        reader
      }
      False -> reader
    }

    Ok(#(reader, is_segwit))
  }
}

/// Peek ahead at the next two bytes to check for SegWit marker/flag.
///
/// Returns `True` if next bytes are 0x00 0x01, `False` on EOF or otherwise.
fn peek_segwit() -> Parser(Bool) {
  fn(reader, ctx) {
    case reader.peek_bytes(reader, 2) {
      Ok(bytes) -> {
        let assert <<marker, flag>> = bytes
        Ok(#(reader, marker == 0x00 && flag == 0x01))
      }

      Error(err) ->
        case err {
          // Ambiguity-aware: do not fail the whole decode just because we couldn't look ahead.
          // Let the later parsing produce a better contextual EOF.
          reader.UnexpectedEof(..) -> Ok(#(reader, False))

          _ ->
            err
            |> ReaderError
            |> new_parse_error(reader)
            |> with_contexts([Field("segwit_discriminator"), ..ctx])
            |> ParseFailed
            |> Error
        }
    }
  }
}

/// Validate and convert the vin_count from U64 to Int, checking structural and policy limits.
fn validate_vin_count(vin_count: U64, max_vin_count_policy: Int) -> Parser(Int) {
  fn(reader, ctx) {
    let min_txin_size = 41
    let remaining = reader.bytes_remaining(reader)

    // Upper bound implied by remaining bytes (each input is at least 41 bytes)
    let max_inputs_by_bytes = remaining / min_txin_size
    // Final max is the stricter of policy vs structural
    let max_inputs = int.min(max_inputs_by_bytes, max_vin_count_policy)

    let decode_err = fn(kind) {
      kind
      |> new_parse_error(reader)
      |> with_contexts([Field("vin_count"), ..ctx])
      |> ParseFailed
    }

    // Convert U64 -> Int, but distinguish "cannot represent" from "range invalid"
    use vin_count_int <- result.try(
      vin_count
      |> u64.to_int
      |> result.map_error(fn(_) {
        vin_count
        |> u64.to_string
        |> IntegerOutOfRange
        |> decode_err
      }),
    )

    // There aren't enough remaining bytes to parse even one input
    use <- bool.lazy_guard(remaining < min_txin_size, fn() {
      InsufficientBytesForInputs(remaining:, min_txin_size:)
      |> decode_err
      |> Error
    })

    case vin_count_int < 1 || vin_count_int > max_inputs {
      True ->
        InvalidValueRange("vin_count", vin_count_int, Some(1), Some(max_inputs))
        |> decode_err
        |> Error

      False -> Ok(#(reader, vin_count_int))
    }
  }
}
