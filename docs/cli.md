# The `ca` command-line tool

The `ca` executable provides registry generation, node files, and batch
indexing. It is a separate Lake package in [`cli/`](../cli/) so that the
`CA` library stays pure Lean; it owns the native dependencies (OpenSSL,
Redis through redis-lean, SQLite through leansqlite) and is built with
`cd cli && lake build` (see [building.md](building.md)).

Run it inside the project it reads, under `lake env` so the project's
whole search path is visible: `lake env ca pack -m MyProject`.

```bash
# Generate registry from @[publish]/@[open_point] annotations
ca registry -m MyProject.Registry -o registry/

# Write the project's node file, and check one
ca pack -m MyProject -o node.sqlite      # --own: every declaration of the module; --all; --no-proofs
ca check node.sqlite

# Load a module, compute addresses, store to Redis
ca fetch -m Mathlib

# Compute addresses and export a JSON manifest
ca address -m Mathlib

# Level 1 canonicalization (reducible-transparency whnf of statements)
ca address --level 1

# Single declaration lookup (checks Redis first, falls back to env)
ca address --name Nat.add_comm

# Ask every source in sources.json about a statement, a coarse hash or a name
ca lookup ByKFv4nqHrcsFWuBFd7ihUXKFNEdMvFdMvjW7n8XE3nn
ca lookup Nat.add_zero --json
ca fetch-sources                         # copy URL sources into .lake/ca/sources

# Check that the OpenSSL hasher agrees with the library's pure SHA-256
ca selftest
```

## `registry`

Generates `declarations.json`, `statements.json` and `meta.json` from `@[publish]` and
`@[open_point]` annotations. Standalone alternative to `#ca_registry` for
environments where the CA binary shares the same toolchain and search
paths — the two produce byte-identical output.

## `pack`

Writes a registry node as one SQLite file
([registry-protocol.md](registry-protocol.md) §12,
[payload.md](payload.md) §6): units and decorations for the chosen
declarations, each with its whole block; a statement unit and an entry
row (status, `type_hash`) per `@[publish]` / `@[open_point]`
declaration; declaration and witness rows. Dependencies are referenced
by id, not packed. Which declarations:

- default: the `@[publish]` / `@[open_point]` ones;
- `--own`: every declaration of the module and its submodules;
- `--all`: every declaration of the loaded environment.

`--no-proofs` packs theorems in statement mode. The imported part of the
reference table is cached under `.lake/ca/`, as for `#ca_registry`. The
packer rebuilds every unit from its own output and reports any member
that does not come back exactly.

## `check`

Checks a node file without trusting it: every unit's ids are recomputed
from its bytes and the file's ref table (no Lean environment needed);
every member, declaration, witness and entry row must agree with its
unit; every decoration must rebuild declarations whose ids, computed
from the names it gives, are the unit's. Reports naming variants and
units with names hashed by name, lists faults, and exits 1 if there are
any. Measured: all of `Init` (65,972 declarations with proofs, 114 MB)
packs in about 2.5 min and checks in about 30 s.

## `lookup`

`ca lookup QUERY` reads the project's `sources.json` ([usage.md](usage.md)
step 6) and asks every source, in order, about `QUERY`: a `stmt` (base58,
32 bytes), a `type_hash` (64 hex digits) or a declaration name. A folder
source answers with its entries (status, `proved_by`, `status_deps`, the
pretty-printed statement). A node file answers with its entries and
their witnesses, and with every declaration bound to the name or
carrying the statement, twins included. `--json` prints one object per
answer. Exit status 2 when nothing answers. `--sources` and `--cache`
override the list and the cache directory.

## `fetch-sources`

Copies every URL source of `sources.json` into `.lake/ca/sources/`
(a folder's `declarations.json`, `meta.json` and `statements.json`; a
node's file), with `curl`. A fetched copy is reused until `--refresh`.
Local sources need no fetch.

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
