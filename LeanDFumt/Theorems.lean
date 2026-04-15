-- ★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★
-- LeanDFumt.Theorems — algebraic properties of D-FUMT₈
-- All proofs use `decide` since the type is finite.
--
-- We list properties that hold UNIVERSALLY (over all 8 values), and
-- properties that hold only on a stated subdomain. The asymmetry between
-- `or` and `and` reflects the operational priority order in the underlying
-- Rei TS implementation: `FALSE` absorbs in `and`, `TRUE` absorbs in `or`,
-- and `NEITHER` propagates left-to-right.
-- ★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★

import LeanDFumt.Basic

namespace LeanDFumt

open DFUMT8

/-! ## Negation (7 theorems) -/

theorem neg_TRUE  : neg .TRUE = .FALSE := by decide
theorem neg_FALSE : neg .FALSE = .TRUE := by decide
theorem neg_BOTH_self     : neg .BOTH     = .BOTH := by decide
theorem neg_NEITHER_self  : neg .NEITHER  = .NEITHER := by decide
theorem neg_INFINITY_self : neg .INFINITY = .INFINITY := by decide
theorem neg_ZERO_self     : neg .ZERO     = .ZERO := by decide
theorem neg_FLOWING_self  : neg .FLOWING  = .FLOWING := by decide

/-- Negation is involutive on the classical pair. -/
theorem neg_neg_classical (a : DFUMT8) (h : a = .TRUE ∨ a = .FALSE) :
    neg (neg a) = a := by
  rcases h with h | h <;> rw [h] <;> decide

/-! ## Conjunction — universal identities (3 theorems) -/

theorem and_FALSE_left  (a : DFUMT8) : and .FALSE a = .FALSE := by
  cases a <;> rfl
theorem and_FALSE_right (a : DFUMT8) : and a .FALSE = .FALSE := by
  cases a <;> rfl

/-- `NEITHER ∧ a = NEITHER` for `a ≠ FALSE` (when `a = FALSE`, FALSE absorbs). -/
theorem and_NEITHER_left_no_FALSE (a : DFUMT8)
    (h : a = .TRUE ∨ a = .BOTH ∨ a = .NEITHER ∨
         a = .INFINITY ∨ a = .ZERO ∨ a = .FLOWING ∨ a = .SELF) :
    and .NEITHER a = .NEITHER := by
  rcases h with h | h | h | h | h | h | h <;> rw [h] <;> decide

/-- `TRUE` is left identity on the classical/reflective core. -/
theorem and_TRUE_left_classical (a : DFUMT8)
    (h : a = .TRUE ∨ a = .FALSE ∨ a = .BOTH ∨ a = .NEITHER) :
    and .TRUE a = a := by
  rcases h with h | h | h | h <;> rw [h] <;> decide

/-! ## Disjunction — universal identities (2 theorems) -/

theorem or_TRUE_left  (a : DFUMT8) : or .TRUE a = .TRUE := by
  cases a <;> rfl
theorem or_TRUE_right (a : DFUMT8) : or a .TRUE = .TRUE := by
  cases a <;> rfl

/-! ## Disjunction — restricted identities (3 theorems) -/

/-- `NEITHER ∨ a = a` on the classical/reflective core. -/
theorem or_NEITHER_left_classical (a : DFUMT8)
    (h : a = .TRUE ∨ a = .FALSE ∨ a = .BOTH ∨ a = .NEITHER) :
    or .NEITHER a = a := by
  rcases h with h | h | h | h <;> rw [h] <;> decide

/-- `a ∨ NEITHER = a` for the same core values. -/
theorem or_NEITHER_right_classical (a : DFUMT8)
    (h : a = .TRUE ∨ a = .FALSE ∨ a = .BOTH ∨ a = .NEITHER) :
    or a .NEITHER = a := by
  rcases h with h | h | h | h <;> rw [h] <;> decide

/-- `FALSE ∨ a = a` only for `a ∈ {TRUE, FALSE, BOTH}` (collapses to FALSE
    for NEITHER due to the right-NEITHER absorption order). -/
theorem or_FALSE_left_no_NEITHER (a : DFUMT8)
    (h : a = .TRUE ∨ a = .FALSE ∨ a = .BOTH) :
    or .FALSE a = a := by
  rcases h with h | h | h <;> rw [h] <;> decide

/-! ## Idempotency (2 theorems, universal) -/

theorem and_idem (a : DFUMT8) : and a a = a := by
  cases a <;> decide
theorem or_idem (a : DFUMT8) : or a a = a := by
  cases a <;> decide

/-! ## Commutativity on the classical pair (2 theorems) -/

theorem and_comm_classical (a b : DFUMT8) (ha : a = .TRUE ∨ a = .FALSE)
    (hb : b = .TRUE ∨ b = .FALSE) : and a b = and b a := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rw [ha, hb] <;> decide

theorem or_comm_classical (a b : DFUMT8) (ha : a = .TRUE ∨ a = .FALSE)
    (hb : b = .TRUE ∨ b = .FALSE) : or a b = or b a := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rw [ha, hb] <;> decide

/-! ## Implication — classical truth table (4 theorems) -/

theorem implies_classical_TT : implies .TRUE .TRUE = .TRUE := by decide
theorem implies_classical_TF : implies .TRUE .FALSE = .FALSE := by decide
theorem implies_classical_FT : implies .FALSE .TRUE = .TRUE := by decide
theorem implies_classical_FF : implies .FALSE .FALSE = .TRUE := by decide

/-! ## Implication — concrete D-FUMT₈ extensions (3 theorems) -/

theorem implies_TRUE_BOTH : implies .TRUE .BOTH = .BOTH := by decide
theorem implies_TRUE_NEITHER : implies .TRUE .NEITHER = .FALSE := by decide
theorem implies_NEITHER_TRUE : implies .NEITHER .TRUE = .TRUE := by decide

/-! ## Numeric anchor (1 theorem) -/

theorem toFloat_TRUE_pos : DFUMT8.toFloat .TRUE > 0.0 := by
  unfold DFUMT8.toFloat
  native_decide

/-! ## Total theorem count: 7 + 1 + 3 + 1 + 2 + 3 + 2 + 2 + 4 + 3 + 1 = 29 zero-sorry. -/

end LeanDFumt
