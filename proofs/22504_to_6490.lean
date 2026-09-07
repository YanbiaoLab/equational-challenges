-- Equation22504 → Equation6490
-- Recorded verdict: false
-- Premise: x = (y ◇ (x ◇ y)) ◇ ((z ◇ z) ◇ y)
-- Conclusion: x = x ◇ (x ◇ ((y ◇ z) ◇ (y ◇ z)))
-- Original submission SHA-256: b29a868d28e9c42fb2f51de233d82aec274f05c90833b0efb06c7bda082f09d3
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib.Tactic

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ y)) ◇ ((z ◇ z) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ (x ◇ ((y ◇ z) ◇ (y ◇ z)))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   
                     

namespace submission

abbrev F := ZMod 7
abbrev G := F × F

def h (a c : F) : F :=
  match a.val, c.val with
  | 0, 0 => 0
  | 0, 1 => 6
  | 0, 2 => 3
  | 0, 3 => 5
  | 0, 4 => 5
  | 0, 5 => 1
  | 0, 6 => 0
  | 1, 0 => 5
  | 1, 1 => 0
  | 1, 2 => 1
  | 1, 3 => 0
  | 1, 4 => 1
  | 1, 5 => 3
  | 1, 6 => 6
  | 2, 0 => 2
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 2
  | 2, 4 => 4
  | 2, 5 => 1
  | 2, 6 => 0
  | 3, 0 => 1
  | 3, 1 => 6
  | 3, 2 => 1
  | 3, 3 => 0
  | 3, 4 => 5
  | 3, 5 => 2
  | 3, 6 => 2
  | 4, 0 => 1
  | 4, 1 => 2
  | 4, 2 => 5
  | 4, 3 => 6
  | 4, 4 => 0
  | 4, 5 => 5
  | 4, 6 => 4
  | 5, 0 => 4
  | 5, 1 => 2
  | 5, 2 => 5
  | 5, 3 => 6
  | 5, 4 => 0
  | 5, 5 => 0
  | 5, 6 => 0
  | 6, 0 => 4
  | 6, 1 => 6
  | _, _ => 0

def op (x y : G) : G :=
  (5 * x.1 + 2 * y.1, 5 * x.2 + 2 * y.2 + h x.1 y.1)

instance magmaG : Magma G := ⟨op⟩

theorem h_identity : ∀ (x y z : F),
    3 * h x y + 5 * h y (5 * x + 2 * y) + 3 * h z z +
      2 * h 0 y + h (3 * x + 2 * y) (2 * y) = 0 := by
  decide

theorem source : EquationLHS G := by
  rintro ⟨xa, xb⟩ ⟨ya, yb⟩ ⟨za, zb⟩
  apply Prod.ext
  · simp only [Magma.op, op]
    linear_combination
      -(7 * ya + 7 * xa + 10 * za) * CharP.cast_eq_zero F 7
  · simp only [Magma.op, op]
    have hz : (5 : F) * za + 2 * za = 0 := by
      linear_combination za * CharP.cast_eq_zero F 7
    have ha : (5 : F) * ya + 2 * (5 * xa + 2 * ya) = 3 * xa + 2 * ya := by
      linear_combination (xa + ya) * CharP.cast_eq_zero F 7
    rw [hz, ha]
    simp only [mul_zero, zero_add]
    have hi := h_identity xa ya za
    linear_combination
      -hi - (h xa ya + h za za + 7 * yb + 7 * xb + 10 * zb) *
        CharP.cast_eq_zero F 7

theorem target_false : ¬ EquationRHS G := by
  intro q
  have bad : ((1, 0) : G) ≠
      (1, 0) ◇ ((1, 0) ◇ (((0, 0) ◇ (0, 0)) ◇ ((0, 0) ◇ (0, 0)))) := by
    decide
  exact bad (q (1, 0) (0, 0) (0, 0))

end submission

def submission : Goal :=
  ⟨submission.G, submission.magmaG, submission.source, submission.target_false⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22504_to_6490 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_22504_to_6490
