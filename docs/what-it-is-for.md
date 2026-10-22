# What CA is for

The unit a mathematician cares about is a result, not a file. CA makes
that unit addressable, which is what the following need:

- **Referencing a result you cannot locate.** You know the statement;
  you do not know the repository, package, module or revision that
  holds it. A statement id is computable from the proposition alone, by
  anyone, without knowing who proved it.
- **Asking "has this already been proved?"** Two libraries that prove
  the same theorem produce the same statement id, so duplication is a
  lookup rather than a literature search. This is the question an agent
  must answer both before starting work and before offering it back.
- **Citing across refactors.** Renaming a declaration, moving it
  between files, reorganising namespaces, or renaming anything it
  references leaves its address unchanged.
- **Knowing when a statement was weakened.** Because a reference is
  embedded by *its own* address, a redefined constant produces a
  different statement id. "This proves the same thing it did before" is
  a comparison of two hashes.
- **Alternative proofs as first-class objects.** Two proofs of one
  theorem share a statement id and differ in their declaration id, so a
  store can hold both instead of overwriting one with the other.
- **Incremental work that stops where mathematics stops.** Since a
  dependent embeds a theorem's *statement*, re-proving a theorem
  invalidates nothing downstream; changing a definition's value
  invalidates everything that could unfold it.
- **Metadata that follows the statement.** A LaTeX rendering, a prose
  description or a translation belongs to a statement, not to a file
  path — keyed by statement id it is written once and shared by every
  proof of it and every project that uses it.
- **Decentralised publication.** Addresses are computed, not assigned:
  no registrar, no coordination, and anyone can verify by re-hashing.

CA is the addressing layer only. Building a store, a verifier or a
registry on top of it is a separate concern — see [Scope and related work](scope.md).
