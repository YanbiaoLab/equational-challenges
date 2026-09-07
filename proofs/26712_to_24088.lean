-- Equation26712 → Equation24088
-- Recorded verdict: false
-- Premise: x = ((x ◇ y) ◇ (y ◇ x)) ◇ (y ◇ x)
-- Conclusion: x = ((x ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)
-- Original submission SHA-256: 49042f9f26d37b023875fca1bf5a1f62d1a48307658f35b25b08780d11aee986
-- Aurora-accepted correction SHA-256: 6eb12013ec0f6879f4edc310ff6e13175d07e0a55bb14d6ce19df910e128aa24
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((x ◇ y) ◇ (y ◇ x)) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((x ◇ y) ◇ y) ◇ ((y ◇ x) ◇ x)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                             
                              

namespace submission

namespace Countermodel

def op (x y : Int) : Int :=
  if x < y then y + 1 else if y < x then y - 1 else x

instance instMagma : Magma Int where
  op := op

theorem source_holds : @EquationLHS Int instMagma := by
  intro x y
  change x = op (op (op x y) (op y x)) (op y x)
  simp only [op]
  split_ifs <;> omega

theorem target_fails : ¬ @EquationRHS Int instMagma := by
  intro target
  have bad := target (-1) 0
  change (-1 : Int) = op (op (op (-1) 0) 0) (op (op 0 (-1)) (-1)) at bad
  simp [op] at bad

end Countermodel

def certificate : Goal :=
  ⟨Int, Countermodel.instMagma, Countermodel.source_holds, Countermodel.target_fails⟩

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_26712_to_24088 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_26712_to_24088
