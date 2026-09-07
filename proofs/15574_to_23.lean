-- Equation15574 → Equation23
-- Recorded verdict: false
-- Premise: x = y ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ y)
-- Conclusion: x = (x ◇ x) ◇ x
-- Original submission SHA-256: a8df8846a7574c1afca3771684f990b543a1427053726d6bf33faa082ed500ee
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = (x ◇ x) ◇ x
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

def affineOp_17_11_1_0 (i j : Fin 17) : Fin 17 :=
  ⟨(11 * i.val + 1 * j.val + 0) % 17, Nat.mod_lt _ (by decide)⟩

end MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 17) := { op := MemoFinOp.affineOp_17_11_1_0 }
  refine ⟨Fin 17, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_15574_to_23 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_15574_to_23
