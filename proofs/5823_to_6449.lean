-- Equation5823 → Equation6449
-- Recorded verdict: false
-- Premise: x = y ◇ (x ◇ (y ◇ ((y ◇ x) ◇ y)))
-- Conclusion: x = x ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))
-- Original submission SHA-256: 14b15b81d94e598ab4905b1c602a855ce3369fd7d2b59f7fb5cbcf077ab731b6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (x ◇ (y ◇ ((y ◇ x) ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = x ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))
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

def affineOp_13_1_11_0 (i j : Fin 13) : Fin 13 :=
  ⟨(1 * i.val + 11 * j.val + 0) % 13, Nat.mod_lt _ (by decide)⟩

end MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 13) := { op := MemoFinOp.affineOp_13_1_11_0 }
  refine ⟨Fin 13, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5823_to_6449 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_5823_to_6449
