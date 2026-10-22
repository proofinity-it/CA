# The `ca` command-line tool

The `ca` executable provides batch indexing and registry generation
commands. It is a separate Lake package in [`cli/`](../cli/) so that the
`CA` library stays pure Lean; it owns the Redis and OpenSSL dependencies
and is built with `cd cli && lake build` (see [building.md](building.md)).

```bash
# Generate registry from @[publish]/@[open_point] annotations
ca registry -m MyProject.Registry -o registry/

# Load a module, compute addresses, store to Redis
ca fetch -m Mathlib

# Compute addresses and export a JSON manifest
ca address -m Mathlib

# Level 1 canonicalization (reducible-transparency whnf of statements)
ca address --level 1

# Single declaration lookup (checks Redis first, falls back to env)
ca address --name Nat.add_comm

# Check that the OpenSSL hasher agrees with the library's pure SHA-256
ca selftest
```

## `registry`

Generates `declarations.json`, `statements.json` and `meta.json` from `@[publish]` and
`@[open_point]` annotations. Standalone alternative to `#ca_registry` for
environments where the CA binary shares the same toolchain and search
paths — the two produce byte-identical output.

## `fetch`

Loads a Lean environment, computes name-based content addresses, and stores
every declaration (name, kind, type, address, dependencies) to Redis.
Requires a running Redis instance. These `ca:decl:*` keys are a local
index for the CLI's own lookups, not a registry node
([registry-protocol.md](registry-protocol.md) §12).

## `address`

Computes name-based content addresses and exports a JSON manifest and
optional TSV edge list. Can also look up a single declaration by name.
Requires a running Redis instance for single-declaration lookups.
