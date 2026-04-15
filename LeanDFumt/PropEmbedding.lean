-- ★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★
-- LeanDFumt.PropEmbedding — embeddings into Bool / Prop / Nat
-- Provides the bridge from D-FUMT₈ to standard Lean 4 reasoning.
-- ★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★

import LeanDFumt.Basic

namespace LeanDFumt

/-! ## Boolean projection

Coarse-grained 8 → 2 collapse: only `TRUE` and `BOTH` (which classically
contain truth) project to `true`. `FALSE` and `NEITHER` project to `false`.
The four dimensional values default to `false` (no classical truth). -/

def DFUMT8.toBool : DFUMT8 → Bool
  | .TRUE | .BOTH => true
  | _             => false

/-! ## Three-valued projection (-1, 0, +1)

Map onto a signed indicator of "truth content":
- TRUE / BOTH → +1
- FALSE / ZERO → 0
- NEITHER → −1
- INFINITY / FLOWING / SELF → 0 (no polar content)
-/

def DFUMT8.toTernary : DFUMT8 → Int
  | .TRUE | .BOTH => 1
  | .FALSE | .ZERO | .INFINITY | .FLOWING | .SELF => 0
  | .NEITHER => -1

/-! ## Proposition embedding

`asProp x` is the classical proposition "x has classical truth content",
i.e. `x = TRUE ∨ x = BOTH`. -/

def DFUMT8.asProp (a : DFUMT8) : Prop :=
  a = .TRUE ∨ a = .BOTH

/-- Decidability of the proposition embedding (uses `DecidableEq DFUMT8`). -/
instance (a : DFUMT8) : Decidable (DFUMT8.asProp a) := by
  unfold DFUMT8.asProp
  exact instDecidableOr

/-! ## Round-trip lemmas (4 theorems) -/

theorem toBool_TRUE  : DFUMT8.toBool .TRUE  = true  := by decide
theorem toBool_FALSE : DFUMT8.toBool .FALSE = false := by decide
theorem toBool_BOTH  : DFUMT8.toBool .BOTH  = true  := by decide
theorem toBool_NEITHER : DFUMT8.toBool .NEITHER = false := by decide

/-! ## Ternary lemmas (3 theorems) -/

theorem toTernary_TRUE     : DFUMT8.toTernary .TRUE = 1 := by decide
theorem toTernary_FALSE    : DFUMT8.toTernary .FALSE = 0 := by decide
theorem toTernary_NEITHER  : DFUMT8.toTernary .NEITHER = -1 := by decide

/-! ## asProp lemmas (4 theorems) -/

theorem asProp_TRUE  : DFUMT8.asProp .TRUE := by
  unfold DFUMT8.asProp; left; rfl

theorem asProp_BOTH  : DFUMT8.asProp .BOTH := by
  unfold DFUMT8.asProp; right; rfl

theorem not_asProp_FALSE : ¬ DFUMT8.asProp .FALSE := by
  unfold DFUMT8.asProp; intro h; rcases h with h | h <;> cases h

theorem not_asProp_NEITHER : ¬ DFUMT8.asProp .NEITHER := by
  unfold DFUMT8.asProp; intro h; rcases h with h | h <;> cases h

/-! ## asProp interacts with `and` and `or` (preserves classical core) -/

theorem asProp_and_TRUE_TRUE :
    DFUMT8.asProp (DFUMT8.and .TRUE .TRUE) := by
  unfold DFUMT8.and DFUMT8.asProp; left; rfl

theorem asProp_or_FALSE_TRUE :
    DFUMT8.asProp (DFUMT8.or .FALSE .TRUE) := by
  unfold DFUMT8.or DFUMT8.asProp; left; rfl

end LeanDFumt
