-- Equation17971 → Equation52356
-- Recorded verdict: false
-- Premise: x = (x ◇ y) ◇ (y ◇ ((z ◇ w) ◇ x))
-- Conclusion: x ◇ y = ((x ◇ (z ◇ y)) ◇ z) ◇ y
-- Original submission SHA-256: a47072425c5c97c69f9f0fbaf76798845ad6fa1239c04c5543b6f5997a2f6407
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ y) ◇ (y ◇ ((z ◇ w) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((x ◇ (z ◇ y)) ◇ z) ◇ y
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
  let m : Magma (Fin 6) := {
    op := finOpTable "[[2, 2, 4, 4, 0, 0], [3, 3, 5, 5, 1, 1], [2, 2, 5, 5, 0, 0], [3, 3, 4, 4, 1, 1], [3, 3, 5, 5, 0, 0], [2, 2, 4, 4, 1, 1]]"
  }
  refine ⟨Fin 6, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_17971_to_52356 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_17971_to_52356
