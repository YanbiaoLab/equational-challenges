-- Equation1648 → Equation19607
-- Recorded verdict: false
-- Premise: x = (x ◇ y) ◇ ((x ◇ y) ◇ y)
-- Conclusion: x = (x ◇ x) ◇ ((x ◇ (x ◇ y)) ◇ y)
-- Original submission SHA-256: 7315c49cd294a01b4d0c578174f954c04bb54312d9a1a510e695ca2bf3181575
-- Aurora-accepted correction SHA-256: 2c9fd032f52adb9ebbe727ee45a345da2120e50a9dd89f2f8dca9c0239e88b40
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ y) ◇ ((x ◇ y) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ x) ◇ ((x ◇ (x ◇ y)) ◇ y)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                             
                              

namespace submission

namespace Countermodel

def op (x y : Int) : Int :=
  if x < y then x - 1 else if y < x then x + 1 else x

instance instMagma : Magma Int where
  op := op

theorem source_holds : @EquationLHS Int instMagma := by
  intro x y
  change x = op (op x y) (op (op x y) y)
  simp only [op]
  split_ifs <;> omega

theorem target_fails : ¬ @EquationRHS Int instMagma := by
  intro target
  have bad := target 0 1
  change (0 : Int) = op (op 0 0) (op (op 0 (op 0 1)) 1) at bad
  simp [op] at bad

end Countermodel

def certificate : Goal :=
  ⟨Int, Countermodel.instMagma, Countermodel.source_holds, Countermodel.target_fails⟩

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1648_to_19607 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_1648_to_19607
