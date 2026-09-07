-- Equation32788 → Equation60009
-- Recorded verdict: false
-- Premise: x = (x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ y
-- Conclusion: (x ◇ x) ◇ y = (x ◇ y) ◇ (x ◇ y)
-- Original submission SHA-256: c7f2e52f5bc3563ca52337b52bfd63ca99e923ad580fc56fff1887f5ac606ebf
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Lean
import Mathlib.Tactic

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), (x ◇ x) ◇ y = (x ◇ y) ◇ (x ◇ y)
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

namespace submission

def h (a c : Nat) : Nat :=
  if a = 0 ∧ c = 0 then 1 else 0

def op (x y : Fin 14) : Fin 14 :=
  let a := (3 * (x.1 / 2) + 5 * (y.1 / 2)) % 7
  let b := ((x.1 % 2) + h (x.1 / 2) (y.1 / 2)) % 2
  ⟨2 * a + b, by
    have ha : a < 7 := Nat.mod_lt _ (by decide)
    have hb : b < 2 := Nat.mod_lt _ (by decide)
    omega⟩

instance magma14 : Magma (Fin 14) := ⟨op⟩

theorem source : EquationLHS (Fin 14) := by decideFin!

theorem target_false : ¬ EquationRHS (Fin 14) := by
  intro q
  have bad := q 0 2
  norm_num [Magma.op, op, h] at bad

end submission

def submission : Goal :=
  ⟨Fin 14, submission.magma14, submission.source, submission.target_false⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32788_to_60009 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_32788_to_60009
