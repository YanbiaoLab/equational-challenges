-- Equation23353 → Equation56679
-- Recorded verdict: false
-- Premise: x = ((y ◇ x) ◇ y) ◇ (x ◇ (x ◇ y))
-- Conclusion: x ◇ (y ◇ x) = (y ◇ (x ◇ x)) ◇ y
-- Original submission SHA-256: eef6162db8d6215f6c9aa3d82da5c8ee808a4e060518e751ad9ff0f0b3abd77f
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Lean

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((y ◇ x) ◇ y) ◇ (x ◇ (x ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (y ◇ x) = (y ◇ (x ◇ x)) ◇ y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Embedded module: JudgeDecide.DecideBang
section
/- decideFin! tactic: decides propositions over finite types by exhaustive checking. -/
           

macro "decideFin!" : tactic => `(tactic| decide)
end

-- Embedded module: JudgeFinOp.MemoFinOp
section
/- finOpTable: build a Magma (Fin n) from a string like "[[0,1],[1,0]]". -/
                       

namespace MemoFinOp

private def extractDigits (s : String) : List Nat :=
  s.toList.filterMap fun c =>
    if c.isDigit then some (c.toNat - '0'.toNat) else none

def finOpTable (s : String) (i j : Fin n) : Fin n :=
  let vals := extractDigits s
  let idx := i.val * n + j.val
  ⟨(vals.getD idx 0) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

end MemoFinOp
end

-- Original submission body
                   
                             
                           
set_option maxRecDepth 1000000
open MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 9) := {
    op := finOpTable "[[0, 7, 5, 2, 6, 4, 1, 8, 3], [3, 5, 8, 5, 0, 7, 4, 2, 6], [6, 4, 0, 8, 3, 1, 7, 5, 0], [4, 2, 6, 6, 1, 8, 5, 0, 7], [7, 5, 0, 6, 2, 2, 8, 3, 1], [1, 8, 3, 0, 7, 6, 2, 6, 4], [8, 3, 1, 7, 5, 0, 3, 4, 2], [2, 6, 4, 1, 8, 3, 0, 8, 5], [5, 0, 7, 4, 2, 6, 3, 1, 3]]"
  }
  refine ⟨Fin 9, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23353_to_56679 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_23353_to_56679
