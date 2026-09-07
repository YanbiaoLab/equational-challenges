-- Equation18395 → Equation29765
-- Recorded verdict: false
-- Premise: x = (y * z) * (x * ((z * y) * z))
-- Conclusion: x = (y * (z * (x * (x * z)))) * y
-- Original submission SHA-256: 185d97a910e5e8e3a271ddd22d5ffdd87a4e9a13e764ed811e5adcebdfb1c032
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ (x ◇ ((z ◇ y) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ (x ◇ (x ◇ z)))) ◇ y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Embedded module: JudgeDecide.DecideBang
section
/- decideFin! tactic: decides propositions over finite types by exhaustive checking. -/
           

macro "decideFin!" : tactic => `(tactic| decide)
end

-- Original submission body
-- stage:stage1.9_rulebook_affine
                   
                             
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace MemoFinOp
def affineOp_17_2_9_0 (i j : Fin 17) : Fin 17 :=
  ⟨(2 * i.val + 9 * j.val + 0) % 17, Nat.mod_lt _ (by decide)⟩
end MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 17) := { op := MemoFinOp.affineOp_17_2_9_0 }
  refine ⟨Fin 17, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_18395_to_29765 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_18395_to_29765
