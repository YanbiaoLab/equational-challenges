-- Equation29366 → Equation48759
-- Recorded verdict: false
-- Premise: x = (x ◇ (y ◇ (y ◇ (z ◇ y)))) ◇ z
-- Conclusion: x ◇ y = ((x ◇ x) ◇ y) ◇ (x ◇ y)
-- Original submission SHA-256: cac62da0c535467f1e11985a01d20d6edb1575b87d3ebac80e94734c800610b5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (y ◇ (y ◇ (z ◇ y)))) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = ((x ◇ x) ◇ y) ◇ (x ◇ y)
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
set_option maxHeartbeats 0
open MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 10) := {
    op := finOpTable "[[5,6,9,4,6,5,7,9,7,4],[2,4,8,5,4,2,9,8,9,5],[1,3,2,6,3,1,5,2,5,6],[8,2,5,3,2,8,4,5,4,3],[7,1,6,0,1,7,3,6,3,0],[0,8,3,1,8,0,2,3,2,1],[9,0,4,2,0,9,6,4,6,2],[4,9,7,8,9,4,0,7,0,8],[3,5,1,7,5,3,8,1,8,7],[6,7,0,9,7,6,1,0,1,9]]"
  }
  refine ⟨Fin 10, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_29366_to_48759 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_29366_to_48759
