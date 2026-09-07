-- Equation6761 → Equation41582
-- Recorded verdict: false
-- Premise: x = y ◇ (x ◇ ((z ◇ z) ◇ (x ◇ y)))
-- Conclusion: x ◇ x = y ◇ (x ◇ (x ◇ (x ◇ y)))
-- Original submission SHA-256: 719f4f419953daf12b5ddc78f76e6e627620d35e20120517e7b0e34e05191d4e
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

-- Embedded module: JudgeMagma.Magma
section
/- Magma class, ◇ notation, and helpers for building finite magmas. -/

class Magma (α : Type _) where
  /-- The binary magma operation, written `◇`. -/
  op : α → α → α

@[inherit_doc] infix:65 " ◇ " => Magma.op

/-- Build a `Magma (Fin n)` from a flat list of values.
    Entry at index `i*n + j` gives the result of `i ◇ j`.
    Usage: `instance : Magma (Fin 3) := magmaFin 3 [0,0,0, 0,0,0, 0,0,1]`

    Marked `@[implicit_reducible]` because Lean 4.32 requires class-valued
    definitions to be transparent to instance resolution. Deliberately not
    plain `@[reducible]`: that would unfold the table literal during general
    unification too, which is pure cost for the large `Fin n` tables here. -/
@[implicit_reducible]
def magmaFin (n : Nat) (table : List Nat) : Magma (Fin n) where
  op a b :=
    let idx := a.val * n + b.val
    ⟨table[idx]! % n, Nat.mod_lt _ (Fin.pos a)⟩
end

-- Embedded module: JudgeProblem
section
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((z ◇ z) ◇ (x ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = y ◇ (x ◇ (x ◇ (x ◇ y)))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   
                     

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace submission

-- search_part:cyclic_skew_product_linear_kernel_v3
abbrev F := ZMod 7
abbrev K := ZMod 3
abbrev G := F × K

def h (a c : F) : K :=
  match a.val, c.val with
  | 1, 2 => 1
  | 2, 4 => 1
  | 4, 1 => 1
  | _, _ => 0

def op (x y : G) : G :=
  (3 * x.1 + 4 * y.1,
   2 * x.2 + 1 * y.2 + h x.1 y.1)

instance magmaG : Magma G := ⟨op⟩

theorem base_identity : ∀ (xa ya za : F),
    xa = (3 * (ya) + 4 * ((3 * (xa) + 4 * ((3 * ((3 * (za) + 4 * (za))) + 4 * ((3 * (xa) + 4 * (ya)))))))) := by
  decide

theorem cocycle_identity : ∀ (xa ya za : F),
    0 = (2 * (0) + 1 * ((2 * (0) + 1 * ((2 * ((2 * (0) + 1 * (0) + h (za) (za))) + 1 * ((2 * (0) + 1 * (0) + h (xa) (ya))) + h ((3 * (za) + 4 * (za))) ((3 * (xa) + 4 * (ya))))) + h (xa) ((3 * ((3 * (za) + 4 * (za))) + 4 * ((3 * (xa) + 4 * (ya))))))) + h (ya) ((3 * (xa) + 4 * ((3 * ((3 * (za) + 4 * (za))) + 4 * ((3 * (xa) + 4 * (ya)))))))) := by
  decide

theorem source : EquationLHS G := by
  rintro ⟨xa, xb⟩ ⟨ya, yb⟩ ⟨za, zb⟩
  apply Prod.ext
  · exact base_identity xa ya za
  · simp only [Magma.op, op]
    have hc := cocycle_identity xa ya za
    linear_combination hc - ((1) * xb + (1) * yb + (2) * zb) * CharP.cast_eq_zero K 3

theorem target_false : ¬ EquationRHS G := by
  intro q
  have bad : (((1, 0) : G) ◇ ((1, 0) : G)) ≠ (((2, 0) : G) ◇ (((1, 0) : G) ◇ (((1, 0) : G) ◇ (((1, 0) : G) ◇ ((2, 0) : G))))) := by
    decide
  exact bad (q ((1, 0) : G) ((2, 0) : G))

end submission

def submission : Goal :=
  ⟨submission.G, submission.magmaG,
    submission.source, submission.target_false⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6761_to_41582 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_6761_to_41582
