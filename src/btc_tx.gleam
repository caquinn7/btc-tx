import gleam/option.{type Option}
import internal/compact_size
import internal/hash32.{type Hash32}
import internal/hex
import internal/reader.{type Reader}

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
    value: String,
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
pub opaque type ParseContext {
  /// The error occurred while parsing the top-level transaction structure.
  ///
  /// This is typically added once at the outermost decode layer.
  Transaction

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
