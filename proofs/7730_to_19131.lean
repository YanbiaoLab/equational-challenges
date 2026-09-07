-- Equation7730 → Equation19131
-- Recorded verdict: false
-- Premise: x = y ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ x))
-- Conclusion: x = (y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ x))
-- Original submission SHA-256: f18fe3b4b3c67d4feae0736426a3bd3010934c400d06817714b61ec179d23cca
-- Aurora-accepted correction SHA-256: 228349b74c79b971a6710f4b35aacd456240b07ae1a939a27ca77a258b3d4025
-- Generator: equational-challenges standalone v2
-- All project definitions are embedded in this file.
import Lean.Elab.Tactic.Omega

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (y ◇ ((y ◇ (y ◇ y)) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ x))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                             

namespace submission

namespace Countermodel

def op (x y : Int) : Int :=
  -2 * x + y + x / 2

instance instMagma : Magma Int where
  op := op

theorem source_holds : @EquationLHS Int instMagma := by
  intro x y
  change x = op y (op y (op (op y (op y y)) x))
  simp only [op]
  omega

theorem target_fails : ¬ @EquationRHS Int instMagma := by
  intro target
  have bad := target 0 (-1)
  change (0 : Int) = op (op (-1) (-1)) (op (op (-1) (-1)) (op (-1) 0)) at bad
  simp [op] at bad

end Countermodel

def certificate : Goal :=
  ⟨Int, Countermodel.instMagma, Countermodel.source_holds, Countermodel.target_fails⟩

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_7730_to_19131 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_7730_to_19131
