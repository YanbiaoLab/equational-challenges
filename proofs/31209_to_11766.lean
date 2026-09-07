-- Equation31209 → Equation11766
-- Recorded verdict: false
-- Premise: x = (y ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y
-- Conclusion: x = x ◇ (((y ◇ x) ◇ x) ◇ (y ◇ x))
-- Original submission SHA-256: 007577101b24fc95e73ad85dca4a41f359c3c472b35541d7103f8661e7b4816d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = x ◇ (((y ◇ x) ◇ x) ◇ (y ◇ x))
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
    op := finOpTable "[[0, 1, 2, 3, 4, 5, 6, 7, 8], [6, 7, 8, 0, 1, 2, 3, 4, 5], [3, 4, 5, 6, 7, 8, 0, 1, 2], [1, 2, 0, 4, 5, 3, 7, 8, 6], [7, 8, 6, 1, 2, 0, 4, 5, 3], [4, 5, 3, 7, 8, 6, 1, 2, 0], [2, 0, 1, 5, 3, 4, 8, 6, 7], [8, 6, 7, 2, 0, 1, 5, 3, 4], [5, 3, 4, 8, 6, 7, 2, 0, 1]]"
  }
  refine ⟨Fin 9, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_31209_to_11766 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_31209_to_11766
