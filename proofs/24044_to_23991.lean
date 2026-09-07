-- Equation24044 → Equation23991
-- Recorded verdict: false
-- Premise: x = ((x ◇ y) ◇ x) ◇ ((x ◇ y) ◇ x)
-- Conclusion: x = ((x ◇ x) ◇ x) ◇ ((x ◇ y) ◇ x)
-- Original submission SHA-256: 9fd96007858090097b28c98ef83907da027a0c7d0915461b182b8877d543eaab
-- Aurora-accepted correction SHA-256: 2614f0445152c7ae19b1bd1afb3d9e28555941f6fda117c10b671d4be9bfd168
-- Generator: equational-challenges standalone v2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((x ◇ y) ◇ x) ◇ ((x ◇ y) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((x ◇ x) ◇ x) ◇ ((x ◇ y) ◇ x)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                     

namespace submission

namespace Equation24044PairTree

inductive V where
  | zero
  | pair (left right : V)
  deriving DecidableEq

def left : V → V
  | .zero => .zero
  | .pair x _ => x

def size : V → Nat
  | .zero => 1
  | .pair x y => size x + size y + 1

theorem size_pos (x : V) : 0 < size x := by
  induction x <;> simp [size, *]

@[simp] theorem pair_ne_right (x y : V) : V.pair x y ≠ y := by
  intro h
  have e := congrArg size h
  have p := size_pos x
  simp [size] at e
  omega

theorem left_fixed {x : V} (h : left x = x) : x = .zero := by
  cases x with
  | zero => rfl
  | pair a b =>
      have e := congrArg size h
      have p := size_pos b
      simp [left, size] at e
      omega

def op (x y : V) : V :=
  if x = y then left x else .pair y x

theorem op_eq_first_zero {x y : V} (h : op x y = x) : x = .zero := by
  by_cases hxy : x = y
  · have fixed : left x = x := by simpa [op, hxy] using h
    exact left_fixed fixed
  · have impossible : V.pair y x = x := by simpa [op, hxy] using h
    exact (pair_ne_right y x impossible).elim

theorem left_op_of_ne {a x : V} (h : a ≠ x) : left (op a x) = x := by
  rw [op, if_neg h]
  rfl

theorem source (x y : V) :
    x = op (op (op x y) x) (op (op x y) x) := by
  rw [show op (op (op x y) x) (op (op x y) x) =
      left (op (op x y) x) by simp [op]]
  by_cases h : op x y = x
  · have hx : x = .zero := op_eq_first_zero h
    subst x
    rw [h]
    rfl
  · exact (left_op_of_ne h).symm

theorem target_not :
    ¬ ∀ x y : V, x = op (op (op x x) x) (op (op x y) x) := by
  intro h
  have bad := h .zero (.pair .zero .zero)
  simp [op, left] at bad

end Equation24044PairTree

def certificate : Goal := by
  refine ⟨Equation24044PairTree.V, ⟨Equation24044PairTree.op⟩, ?_, ?_⟩
  · exact Equation24044PairTree.source
  · exact Equation24044PairTree.target_not

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_24044_to_23991 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_24044_to_23991
