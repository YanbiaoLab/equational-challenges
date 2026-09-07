-- Equation23806 → Equation59159
-- Recorded verdict: false
-- Premise: x = ((y ◇ z) ◇ z) ◇ (z ◇ (x ◇ y))
-- Conclusion: (x ◇ x) ◇ y = y ◇ ((x ◇ x) ◇ y)
-- Original submission SHA-256: 36a1ab14c4576d03c9d79546c0448456ca9b1780c1075c90375461c7c8d4a60b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ z) ◇ (z ◇ (x ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), (x ◇ x) ◇ y = y ◇ ((x ◇ x) ◇ y)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Embedded module: JudgeDecide.DecideBang
section
/- decideFin! tactic: decides propositions over finite types by exhaustive checking. -/
           

macro "decideFin!" : tactic => `(tactic| decide)
end

-- Original submission body
                   
                             

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace MemoFinOp

def affineOp_19_17_3_0 (i j : Fin 19) : Fin 19 :=
  ⟨(17 * i.val + 3 * j.val + 0) % 19, Nat.mod_lt _ (by decide)⟩

end MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 19) := { op := MemoFinOp.affineOp_19_17_3_0 }
  refine ⟨Fin 19, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23806_to_59159 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_23806_to_59159
