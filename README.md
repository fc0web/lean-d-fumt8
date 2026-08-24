# LeanDFumt — Eight-Valued Logic Library for Lean 4

[![Lean 4](https://img.shields.io/badge/Lean-v4.27.0-blue)](https://lean-lang.org)
[![License: Apache-2.0](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)

An open-source Lean 4 library implementing the **D-FUMT₈ eight-valued logic**
of the Rei-AIOS project, with kernel-checked algebraic properties and
classical-logic embeddings.

**No Mathlib dependency** — pure Lean 4, builds in seconds.

## What is D-FUMT₈?

The Rei-AIOS D-FUMT₈ logic distinguishes eight discrete truth values:

| Value     | Meaning                                          | Quantum analog                |
|-----------|--------------------------------------------------|-------------------------------|
| TRUE      | classical true                                   | `|1⟩` qubit                   |
| FALSE     | classical false                                  | `|0⟩` qubit                   |
| BOTH      | both true and false (paraconsistent)             | `|+⟩` superposition           |
| NEITHER   | neither true nor false (paracomplete)            | `I/2` maximally mixed         |
| INFINITY  | unbounded / dimensional infinity                 | Fock tower (gap-invariant)    |
| ZERO      | absence (distinct from FALSE)                    | bosonic vacuum (`⟨n̂⟩ = 0`)    |
| FLOWING   | dynamical / flowing state                        | Bell-reduced state            |
| SELF      | self-referential / idempotent                    | projector `P = |ψ⟩⟨ψ|`        |

The logic was introduced and developed in:

- **Paper 69** (Schnorr–D-FUMT₈ correspondence): [DOI 10.5281/zenodo.19562346](https://doi.org/10.5281/zenodo.19562346)
- **Paper 75** (Quantum D-FUMT₈ single-qubit): [DOI 10.5281/zenodo.19595292](https://doi.org/10.5281/zenodo.19595292)
- **Paper 76** (Quantum D-FUMT₈ multi-mode Fock): [DOI 10.5281/zenodo.19595582](https://doi.org/10.5281/zenodo.19595582)
- **Paper 77** (this Lean library): forthcoming

This Lean 4 library is the **proof-theoretic anchor** complementing the
QuTiP-based numerical anchor of Papers 75/76.

## Files

```
LeanDFumt/
  Basic.lean           inductive DFUMT8 + neg / and / or / implies + sanity
  Theorems.lean        29 zero-sorry algebraic properties (decide-proved)
  PropEmbedding.lean   embeddings into Bool / Int / Prop with bridge lemmas
LeanDFumt.lean         re-exports
lakefile.toml          Lake project manifest
lean-toolchain         leanprover/lean4:v4.27.0
LICENSE                Apache-2.0
```

## Quick start

```bash
git clone https://github.com/fc0web/lean-d-fumt8
cd lean-d-fumt8
lake build           # ~5 seconds (no Mathlib)
```

Use in your project's `lakefile.toml`:

```toml
[[require]]
name = "LeanDFumt"
git = "https://github.com/fc0web/lean-d-fumt8"
rev = "v1.0.0"
```

Then in your Lean source:

```lean
import LeanDFumt

open LeanDFumt
open LeanDFumt.Notation

example : DFUMT8.and .BOTH .TRUE = .BOTH := by decide
example : ¬d .BOTH = .BOTH := by decide
example : (.TRUE ∨d .NEITHER) = .TRUE := by decide
```

## Documentation

Companion pages published under [`docs/`](docs/) via GitHub Pages:

- **[Error Database](https://fc0web.github.io/lean-d-fumt8/)** — 15 common Lean 4 errors, each with a minimal reproduction and a fix that preserves the zero-sorry, no-Mathlib discipline. Cross-references the `CHECKER_SPEC` locators. English.
- **[Your first Lean 4 proof](https://fc0web.github.io/lean-d-fumt8/first-proof.html)** — a five-move interactive tutorial for readers who have never opened a proof assistant. Ten minutes, no installation, runs statically in the browser. Also available in [日本語](https://fc0web.github.io/lean-d-fumt8/first-proof-ja.html).
- **[Agent verification, formally](https://fc0web.github.io/lean-d-fumt8/agent-verification.html)** — a note on why sampling-based agent evaluation is a floor not a ceiling, with a complete Lean 4 harness proof in ~40 lines. English.

## Design choices

### Why no Mathlib dependency?

Mathlib is wonderful but heavy: the standard build pulls hundreds of
dependencies and takes 30+ minutes on first cache miss. For an 8-element
finite logic, **everything is decidable by `by decide`**, so no Mathlib
machinery is needed. This keeps the library light, fast to build, and
easy to embed in any Lean 4 project.

### Why `noncomputable` is not used

All operations on `DFUMT8` are pattern-matchable on a finite inductive,
so they are fully computable. `decide` and `native_decide` work for
every algebraic claim.

### Asymmetric semantics

The `and` and `or` operations have priority orderings that match Rei's
TypeScript implementation (`src/axiom-os/seven-logic.ts` in the main
private repo). Specifically:

- **In `and`**: `FALSE` absorbs (any position), then `NEITHER` propagates,
  then classical / dimensional rules apply.
- **In `or`**: `TRUE` absorbs, then `NEITHER` is left identity (with `FALSE`
  retaining priority on the right), then classical / dimensional rules.

Because of this asymmetric priority, some "obvious" equations like
`NEITHER ∧ a = NEITHER` hold for *most* `a` but fail for `a = FALSE`
(where FALSE wins). All such restrictions are honestly stated in the
theorem hypotheses — see `Theorems.lean`.

## Theorem inventory

29 zero-sorry theorems across:

- **Negation** (8): involution, idempotents
- **Conjunction** (4): FALSE absorption, restricted NEITHER, classical TRUE identity
- **Disjunction** (5): TRUE absorption, restricted NEITHER and FALSE identities
- **Idempotency** (2): `a ∧ a = a`, `a ∨ a = a` (universal)
- **Commutativity** (2): on the classical pair {TRUE, FALSE}
- **Implication** (7): full classical truth table + 3 D-FUMT₈ extensions
- **Numeric anchor** (1): `toFloat TRUE > 0`

All proved by `decide` / `native_decide` on the finite type.

## Bridge to standard logic

`PropEmbedding.lean` provides three explicit bridges:

1. **`DFUMT8.toBool : DFUMT8 → Bool`** — coarse 8 → 2 collapse (TRUE/BOTH map to true)
2. **`DFUMT8.toTernary : DFUMT8 → Int`** — signed indicator (-1 / 0 / +1)
3. **`DFUMT8.asProp : DFUMT8 → Prop`** — proposition `a = TRUE ∨ a = BOTH`

Decidability instance is provided so existing Lean 4 / Mathlib reasoning
can interoperate with `DFUMT8` values via these bridges.

## Citation

```bibtex
@misc{fujimoto2026leandfumt,
  author = {Fujimoto, Nobuki},
  title  = {LeanDFumt: Eight-Valued Logic Library for Lean 4},
  year   = 2026,
  doi    = {forthcoming},
  url    = {https://github.com/fc0web/lean-d-fumt8},
  note   = {Companion to Rei-AIOS Papers 69, 75, 76, 77.}
}
```

## License

Apache License 2.0 — see [LICENSE](LICENSE) for full text.

This library is part of the broader Rei-AIOS open-science effort by Nobuki
Fujimoto. The main Rei-AIOS repository (`fc0web/rei-aios`) is private; this
library and the related Paper 71 / 72 reproducibility packages are the
public artifacts.

## Contact

- GitHub: [fc0web](https://github.com/fc0web)
- note.com: [nifty_godwit2635](https://note.com/nifty_godwit2635)

## See also

- [Rei-AIOS Paper 71 reproducibility demo](https://github.com/fc0web/rei-shannon-demo)
- [Rei-AIOS Paper 72 semantic complexity demo](https://github.com/fc0web/rei-semantic-complexity)
