-- Equation38124 → Equation26723
-- Recorded verdict: false
-- Premise: x = ((x ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ y
-- Conclusion: x = ((x ◇ y) ◇ (y ◇ y)) ◇ (y ◇ y)
-- Original submission SHA-256: 3ed45cd3f1df34a147ac9dbacf1fe07fc673f0f90c37601eaea8d3b23250de05
-- Aurora-accepted correction SHA-256: 87f151c733e0dd7a5f1aca235d80441efa0e8e771acfca2bcc8f3a8e2c315cc2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((x ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((x ◇ y) ◇ (y ◇ y)) ◇ (y ◇ y)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                             

namespace submission

namespace Countermodel

def op (x y : Int) : Int :=
  x - 2 * y + y / 2

instance instMagma : Magma Int where
  op := op

theorem source_holds : @EquationLHS Int instMagma := by
  intro x y
  change x = op (op (op x (op (op y y) y)) y) y
  simp only [op]
  omega

theorem target_fails : ¬ @EquationRHS Int instMagma := by
  intro target
  have bad := target 0 (-1)
  change (0 : Int) = op (op (op 0 (-1)) (op (-1) (-1))) (op (-1) (-1)) at bad
  simp [op] at bad

end Countermodel

def certificate : Goal :=
  ⟨Int, Countermodel.instMagma, Countermodel.source_holds, Countermodel.target_fails⟩

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_38124_to_26723 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_38124_to_26723
