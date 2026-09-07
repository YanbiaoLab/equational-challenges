-- Equation32199 → Equation22919
-- Recorded verdict: false
-- Premise: x = (y * ((x * (z * z)) * y)) * z
-- Conclusion: x = (y * (z * z)) * ((y * z) * x)
-- Original submission SHA-256: 19069847d4e0345dd70e4bfdf8c1db86a827e1cb0a972f6ccfbc1832977fc30f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ ((x ◇ (z ◇ z)) ◇ y)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ z)) ◇ ((y ◇ z) ◇ x)
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
def affineOp_43_32_22_0 (i j : Fin 43) : Fin 43 :=
  ⟨(32 * i.val + 22 * j.val) % 43, Nat.mod_lt _ (by decide)⟩
def scale16_43 (u : Fin 43) : Fin 43 :=
  ⟨(16 * u.val) % 43, Nat.mod_lt _ (by decide)⟩
end MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 43) := { op := MemoFinOp.affineOp_43_32_22_0 }
  refine ⟨Fin 43, m, ?_⟩
  constructor
  · have hc : ∀ u y : Fin 43, m.op y (m.op u y) = MemoFinOp.scale16_43 u := by
      decideFin!
    have hf : ∀ x z : Fin 43, m.op (MemoFinOp.scale16_43 (m.op x (m.op z z))) z = x := by
      decideFin!
    intro x y z
    rw [hc]
    exact (hf x z).symm
  · decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32199_to_22919 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_32199_to_22919
