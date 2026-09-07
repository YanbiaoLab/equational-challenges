-- Equation25260 → Equation99
-- Recorded verdict: false
-- Premise: x = (y ◇ (y ◇ (y ◇ x))) ◇ (y ◇ x)
-- Conclusion: x = x ◇ ((x ◇ x) ◇ x)
-- Original submission SHA-256: ff1c35dae070e5b927dde15d3708616bde88e6b8b57385287bb9715e96d5d982
-- Aurora-accepted correction SHA-256: cbb10fe0f0ba4b13ad9d8a94759e5cc9a4952181dba95611af226f825997ca99
-- Generator: equational-challenges standalone v2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ (y ◇ (y ◇ x))) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = x ◇ ((x ◇ x) ◇ x)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                             
                              

namespace submission

namespace Countermodel

def op (x y : Int) : Int :=
  if x < y then y + 1 else if y < x then y - 1 else x - 1

instance instMagma : Magma Int where
  op := op

theorem source_holds : @EquationLHS Int instMagma := by
  intro x y
  change x = op (op y (op y (op y x))) (op y x)
  simp only [op]
  split_ifs <;> omega

theorem target_fails : ¬ @EquationRHS Int instMagma := by
  intro target
  have bad := target (-1)
  change (-1 : Int) = op (-1) (op (op (-1) (-1)) (-1)) at bad
  simp [op] at bad

end Countermodel

def certificate : Goal :=
  ⟨Int, Countermodel.instMagma, Countermodel.source_holds, Countermodel.target_fails⟩

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_25260_to_99 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_25260_to_99
