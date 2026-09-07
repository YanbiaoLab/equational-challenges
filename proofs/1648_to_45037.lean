-- Equation1648 → Equation45037
-- Recorded verdict: false
-- Premise: x = (x ◇ y) ◇ ((x ◇ y) ◇ y)
-- Conclusion: x ◇ x = x ◇ (((x ◇ x) ◇ x) ◇ x)
-- Original submission SHA-256: fddb82aa1d1ebb46d609219c09411aa500d9a7d7018c101dbe00b0b0e9b324c8
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib.Tactic.NormNum
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ y) ◇ ((x ◇ y) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x ◇ x = x ◇ (((x ◇ x) ◇ x) ◇ x)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   
                     

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace submission

-- search_part:guarded_residue_selector
def op (x y : Int) : Int :=
  if x < y then x + -1 else if y < x then x + 1 else x + -1

instance instMagma : Magma Int where
  op := op

theorem source_holds : @EquationLHS Int instMagma := by
  intro x y
  change x = op (op (x) (y)) (op (op (x) (y)) (y))
  simp only [op]
  split_ifs <;> omega

theorem target_fails : ¬ @EquationRHS Int instMagma := by
  intro target
  have bad := target (-2)
  change op ((-2)) ((-2)) = op ((-2)) (op (op (op ((-2)) ((-2))) ((-2))) ((-2))) at bad
  norm_num [op] at bad

end submission

def submission : Goal :=
  ⟨Int, submission.instMagma,
    submission.source_holds, submission.target_fails⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1648_to_45037 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_1648_to_45037
