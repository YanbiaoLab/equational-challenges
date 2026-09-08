-- Equation32030 → Equation54180
-- Recorded verdict: false
-- Premise: x = (x ◇ ((y ◇ (z ◇ y)) ◇ y)) ◇ y
-- Conclusion: x ◇ (y ◇ y) = x ◇ (y ◇ (z ◇ w))
-- Original submission SHA-256: e3847350e8dab4271ef67cf7086b058ce35860a89d6633dcbca55f138025da46
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ ((y ◇ (z ◇ y)) ◇ y)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = x ◇ (y ◇ (z ◇ w))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   
                             
                              
namespace submission
def op (x y : Nat) : Nat :=
  if x % 2 = y % 2 then x - 1 else x + 1
instance instMagma : Magma Nat where op := op
theorem source_holds : @EquationLHS Nat instMagma := by
  intro q0 q1 q2
  change q0 = (op (op q0 (op (op q1 (op q2 q1)) q1)) q1)
  simp only [op] <;> split_ifs <;> omega
theorem target_fails : ¬ @EquationRHS Nat instMagma := by
  intro target
  have bad := target 0 0 2 0
  change (op 0 (op 0 0)) = (op 0 (op 0 (op 2 0))) at bad
  simp [op] at bad
end submission
def submission : Goal :=
  ⟨Nat, submission.instMagma, submission.source_holds, submission.target_fails⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32030_to_54180 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_32030_to_54180
