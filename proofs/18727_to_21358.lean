-- Equation18727 → Equation21358
-- Recorded verdict: false
-- Premise: x = (x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))
-- Conclusion: x = (x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))
-- Original submission SHA-256: 1f1351bde50cab853d9c72d741c43b286c4fd357226f36b2985de14037727c40
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib.Tactic.NormNum

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = (x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = (x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   
                     

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace submission

-- search_part:linear_floor
def op (x y : Int) : Int :=
  -1*x + 0*y + -1*((1*x + 1*y + 0) / 2) + 0

instance instMagma : Magma Int where
  op := op

theorem source_holds : @EquationLHS Int instMagma := by
  intro x
  change x = op (op (x) (x)) (op (op (x) (x)) (op (x) (x)))
  simp only [op]
  omega

theorem target_fails : ¬ @EquationRHS Int instMagma := by
  intro target
  have bad := target (-1)
  change (-1) = op (op ((-1)) (op ((-1)) ((-1)))) (op ((-1)) (op ((-1)) ((-1)))) at bad
  norm_num [op] at bad

end submission

def submission : Goal :=
  ⟨Int, submission.instMagma,
    submission.source_holds, submission.target_fails⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_18727_to_21358 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_18727_to_21358
