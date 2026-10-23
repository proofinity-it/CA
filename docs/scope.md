# Where CA is used, and what it is not

CA is the addressing layer. It computes ids and can generate a
project-local registry folder; it does not store declarations, run the
kernel, or serve queries.

- [canode](https://github.com/proofinity-it/canode) (declbuild until
  2026-10-23) builds on it: the live node of CA, a declaration-granular
  store keyed by these ids, a kernel re-checker that re-verifies a
  stored declaration against an explicitly trusted cone, statement-keyed
  annotations, and node export / import of the same file. Public release
  intended shortly.

## Related work

[LeanArchitect](https://github.com/hanwenzhu/LeanArchitect) (Zhu et
al., ITP 2026) predates this repository and is worth reading before this one. It
extracts a *blueprint* — the informal-statement dependency graph that
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) projects
plan with — directly from Lean source: declarations carry a
`@[blueprint]` attribute, the edges between nodes are inferred from the
elaborated declarations instead of being maintained by hand in LaTeX,
and the result is exported as JSON and LaTeX with progress trackable by
humans and by provers. It does two things this library does not: it
keeps a human-authored mathematical narrative attached to formal code,
and it fits a workflow mathematicians already use.

It is complementary rather than competing. A blueprint node is
identified by name plus an author-chosen label and lives in one
repository, so it is exactly as portable as that project's names; a
content address belongs to no repository but authors nothing. If a
blueprint node recorded the statement ids of the declarations that
discharge it, the node would survive renames and become comparable
across projects — and its informal text is the best available content
for anything keyed by statement rather than by file path.

## What an address covers, and what it cannot

An address is a hash of a *canonical form*, so the honest question is
never "is it exact?" but "what does the canonical form erase?".

**Erased by construction (L0).** Binder names (de Bruijn), universe
parameter names (renamed positionally from the declaration's universe
binder list — renaming binders is erased, reordering them is not,
since use sites instantiate levels positionally), the syntactic form of
universe levels (`max u v` and `max v u`, `max u u` and `u` are
normalised to one representative), `mdata` and source positions, the
declaration's own name, and — because `RefHash` embeds each reference by
*its* id — the names of everything it refers to, wherever those live and
however they were later renamed or moved. Two structurally
identical declarations therefore coincide even across libraries, under
whatever names each of them chose. For a *reference* to a theorem the
proof is erased as well, by proof irrelevance, so re-proving a theorem
changes nothing for anything that uses it.

**Why de Bruijn is enough here, and where it would not be.** An
address is only ever computed for a *closed* term: a declaration's type
or value has no free variables (Lean's `Expr` is locally nameless, and
stored constants contain no `fvar` and no loose `bvar`), and universe
parameters are renamed positionally. For closed terms the de Bruijn
form is a canonical representative — two closed terms are α-equivalent
exactly when their de Bruijn trees are equal — so α-equivalence is
handled by the representation at the declaration level. That stops
being true for *open* subterms: a fragment under different enclosing
binders gets different de Bruijn indices, which is the problem
[Hashing Modulo Alpha-Equivalence](https://simon.peytonjones.org/assets/pdfs/hashing-modulo-alpha.pdf)
(Maziarz, Ellis, Lawrence, Fitzgibbon, Peyton Jones, PLDI 2021) solves.
CA does hash subterms on the way up — the banner shows them, and they
are memoised across declarations — but those subterm ids are a cache
keyed on de Bruijn structure, not addresses of fragments: the id of
`bvar 0` is the same whatever variable it denotes. Addressing open
fragments (search by type pattern, sharing a subterm across
declarations) would need that paper's construction, and whether its
normalisation can be made Merkle-compositional is an open question.

**Erased with L1.** Reducible-transparency `whnf` before hashing:
`abbrev`s, `@[reducible]` definitions and type synonyms collapse, so
statements that differ only by such a synonym share an address.

**Not erased today, but reachable by more normalisation.** Binder info
currently enters the hash, and a level that ignored it would merge API
variants stating the same proposition. Unfolding at *default*
transparency would merge more; Lean's kernel decides that equality
pairwise, but hashing needs a canonical representative, and normalising
at default transparency neither terminates cheaply nor stays stable
across library refactors — which is why L1 stops at reducible.
Structure-eta and instance-argument normalisation sit in the same
category: possible, each with a cost in time and in false merges.

**Not reachable by any normal form.** Two genuinely different
formalisations of the same mathematics are related by a *proof*, not by
a normal form, and finding that proof is theorem proving. No hashing
scheme will merge them, and one that appeared to would be lying.

The productive way to cover that last case is to record it rather than
hash it: a proof of `A ↔ B` is itself a declaration with its own
address, so "these two statements are equivalent, and here is the
term that shows it" becomes ordinary data in the same store, checkable
by the same kernel. Search layers (type fingerprints, embeddings) can
propose such links; only a proof establishes one.

**Operationally**: identity is exact with respect to the toolchain's
core, since references are by id — a change in Lean's core propagates
upward, where the older name-based hash was stable precisely because it
was blind. And computing ids for a whole Mathlib-sized environment is a
single-threaded pass of minutes, worth caching.
