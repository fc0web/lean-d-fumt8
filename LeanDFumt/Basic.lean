-- ★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★
-- LeanDFumt.Basic — D-FUMT₈ inductive type and core operations
-- ★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★

namespace LeanDFumt

/-! ## D-FUMT₈ — eight truth values

The Rei-AIOS D-FUMT₈ logic distinguishes eight discrete truth values, of which
the first five form the operational core and the last three encode reflective /
dimensional structure:

| Value     | Numeric anchor (Rei) | Quantum analog (Paper 75)            |
|-----------|---------------------:|--------------------------------------|
| TRUE      | 1.0                  | `|1⟩` qubit                           |
| FALSE     | 0.0                  | `|0⟩` qubit                           |
| BOTH      | 2.0                  | `|+⟩` superposition                   |
| NEITHER   | -1.0                 | `I/2` maximally mixed                 |
| INFINITY  | 3.0                  | Fock tower (gap-invariant)            |
| ZERO      | 4.0                  | bosonic vacuum (`⟨n̂⟩ = 0`)            |
| FLOWING   | 5.0                  | Bell-reduced state                    |
| SELF      | 6.0                  | projector `P = |ψ⟩⟨ψ|` (`P² = P`)     |
-/

inductive DFUMT8 : Type where
  | TRUE
  | FALSE
  | BOTH
  | NEITHER
  | INFINITY
  | ZERO
  | FLOWING
  | SELF
  deriving Repr, DecidableEq, Inhabited

/-! ## Numeric anchor (matches Rei TS implementation `seven-logic.ts`). -/

def DFUMT8.toFloat : DFUMT8 → Float
  | .TRUE     => 1.0
  | .FALSE    => 0.0
  | .BOTH     => 2.0
  | .NEITHER  => -1.0
  | .INFINITY => 3.0
  | .ZERO     => 4.0
  | .FLOWING  => 5.0
  | .SELF     => 6.0

/-! ## Negation

In classical logic `¬ TRUE = FALSE` and vice versa. The four reflective
values are fixed under involutive negation in the Rei convention: `BOTH`
(both true and false) negates to itself, `NEITHER` (neither) likewise; the
dimensional values `INFINITY / ZERO / FLOWING / SELF` are also their own
negations because their meaning is dimensional, not polar.
-/

def DFUMT8.neg : DFUMT8 → DFUMT8
  | .TRUE     => .FALSE
  | .FALSE    => .TRUE
  | .BOTH     => .BOTH
  | .NEITHER  => .NEITHER
  | .INFINITY => .INFINITY
  | .ZERO     => .ZERO
  | .FLOWING  => .FLOWING
  | .SELF     => .SELF

/-! ## Conjunction (∧) and disjunction (∨)

We use the operational meet/join inherited from the Rei TS implementation:

- `TRUE ∧ x = x`, `FALSE ∧ x = FALSE`,
- `BOTH ∧ x = x` (BOTH absorbs through),
- `NEITHER ∧ x = NEITHER` (NEITHER propagates),
- Dimensional values default to `NEITHER` when meeting another dimensional
  value (no operational ground), but pass classical values through.

This matches the table in `src/axiom-os/seven-logic.ts` of the Rei-AIOS
codebase (TS version), now machine-checked in Lean 4.
-/

def DFUMT8.and : DFUMT8 → DFUMT8 → DFUMT8
  | .FALSE, _ => .FALSE
  | _, .FALSE => .FALSE
  | .NEITHER, _ => .NEITHER
  | _, .NEITHER => .NEITHER
  | .TRUE, b => b
  | a, .TRUE => a
  | .BOTH, b => b
  | a, .BOTH => a
  | a, b => if a == b then a else .NEITHER

def DFUMT8.or : DFUMT8 → DFUMT8 → DFUMT8
  | .TRUE, _ => .TRUE
  | _, .TRUE => .TRUE
  | .NEITHER, b => b
  | a, .NEITHER => a
  | .FALSE, b => b
  | a, .FALSE => a
  | .BOTH, _ => .BOTH
  | _, .BOTH => .BOTH
  | a, b => if a == b then a else .BOTH

/-! ## Implication

Material implication `a → b` is defined as `(¬ a) ∨ b`. -/

def DFUMT8.implies (a b : DFUMT8) : DFUMT8 :=
  DFUMT8.or (DFUMT8.neg a) b

/-! ## Notation -/

namespace Notation
  scoped notation:50 a " ∧d " b => DFUMT8.and a b
  scoped notation:40 a " ∨d " b => DFUMT8.or a b
  scoped notation:25 a " →d " b => DFUMT8.implies a b
  scoped prefix:80 "¬d " => DFUMT8.neg
end Notation

/-! ## Sanity computations (`#eval`-friendly). -/

example : DFUMT8.and .TRUE .TRUE = .TRUE := by decide
example : DFUMT8.and .TRUE .FALSE = .FALSE := by decide
example : DFUMT8.and .BOTH .TRUE = .BOTH := by decide
example : DFUMT8.and .BOTH .FALSE = .FALSE := by decide
example : DFUMT8.and .NEITHER .TRUE = .NEITHER := by decide
example : DFUMT8.or .FALSE .FALSE = .FALSE := by decide
example : DFUMT8.or .NEITHER .NEITHER = .NEITHER := by decide
example : DFUMT8.or .NEITHER .TRUE = .TRUE := by decide
example : DFUMT8.neg (DFUMT8.neg .TRUE) = .TRUE := by decide
example : DFUMT8.neg .BOTH = .BOTH := by decide

end LeanDFumt
