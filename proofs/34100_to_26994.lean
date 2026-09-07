-- Equation34100 → Equation26994
-- Recorded verdict: false
-- Premise: x = ((y * y) * (z * (z * x))) * z
-- Conclusion: x = ((y * y) * (x * z)) * (x * x)
-- Original submission SHA-256: 695847f958bc1895f340219aa0b9dd39c7f35c6faff4bd1996e60b2cf8290c3c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ (z ◇ (z ◇ x))) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ (x ◇ z)) ◇ (x ◇ x)
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
-- stage:stage1.91_rulebook_affine_n9_micro_orbit_table
                   
                             
                           

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 9) := {
    op := finOpTable "[[0,6,3,5,2,8,7,4,1],[3,0,6,8,5,2,1,7,4],[6,3,0,2,8,5,4,1,7],[7,4,1,0,6,3,5,2,8],[1,7,4,3,0,6,8,5,2],[4,1,7,6,3,0,2,8,5],[5,2,8,7,4,1,0,6,3],[8,5,2,1,7,4,3,0,6],[2,8,5,4,1,7,6,3,0]]"
  }
  refine ⟨Fin 9, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_34100_to_26994 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_34100_to_26994
