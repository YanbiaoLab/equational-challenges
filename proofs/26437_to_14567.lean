-- Equation26437 → Equation14567
-- Recorded verdict: false
-- Premise: x = (y * ((z * z) * z)) * (x * y)
-- Conclusion: x = y * (((x * x) * (z * x)) * z)
-- Original submission SHA-256: 31f4e464c32f96a42112f18ddb7108d74abaa1d9a9bba6dca5fbb1c796a461da
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ ((z ◇ z) ◇ z)) ◇ (x ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ z)
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
    op := finOpTable "[[0,4,8,1,5,6,2,3,7],[3,7,2,4,8,0,5,6,1],[6,1,5,7,2,3,8,0,4],[7,2,3,8,0,4,6,1,5],[1,5,6,2,3,7,0,4,8],[4,8,0,5,6,1,3,7,2],[5,6,1,3,7,2,4,8,0],[8,0,4,6,1,5,7,2,3],[2,3,7,0,4,8,1,5,6]]"
  }
  refine ⟨Fin 9, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_26437_to_14567 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_26437_to_14567
