# btc_tx

A reference-oriented library for parsing and modeling ₿itcoin transaction data.

> ⚠️ **Status:** This library is under active development and is not yet ready for general use.

<!-- [![Package Version](https://img.shields.io/hexpm/v/btc_tx)](https://hex.pm/packages/btc_tx)
[![Hex Docs](https://img.shields.io/badge/hex-docs-ffaff3)](https://hexdocs.pm/btc_tx/) -->

## Goals & Philosophy

This library is guided by a small set of principles:

- **Correctness over convenience**  
  Malformed or ambiguous transaction encodings are surfaced explicitly rather than being silently normalized or partially parsed.

- **Reference-grade intent**  
  The library is structured so it can be read alongside Bitcoin documentation as a reliable guide to how transactions are laid out on the wire.

- **Faithful modeling of the protocol**  
  Protocol distinctions and transaction forms are preserved rather than collapsed into convenience abstractions.

This library is intended for educational and infrastructure use.
It parses and models Bitcoin transaction data, including basic serialization
and format checks, but does not perform full transaction validation such as
script evaluation, signature verification, or UTXO-contextual consensus rules.
No security guarantees are provided.

<!-- ```sh
gleam add btc_tx@1
``` -->
```gleam
import btc_tx

pub fn main() -> Nil {
  // Example usage will be added as the API stabilizes.
}
```

<!-- Further documentation can be found at <https://hexdocs.pm/btc_tx>. -->

## Development

```sh
gleam test -t javascript  # Run tests on the JS target
gleam test -t erlang  # Run tests on the Erlang target
```
