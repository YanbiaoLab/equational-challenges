-- Equation11051 → Equation10201
-- Recorded verdict: false
-- Premise: x = y ◇ ((x ◇ (x ◇ y)) ◇ (y ◇ y))
-- Conclusion: x = y ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ y))
-- Original submission SHA-256: 163d1a5b916ba5c534df1d2845816e5964b7227d8616cfbaa7a2efa617f0f80f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ ((x ◇ (x ◇ y)) ◇ (y ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ y))
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
  match a, c with
  | 0, 1 | 0, 2 | 0, 4 | 1, 5 | 2, 3 | 4, 6 => 3
  | 1, 0 | 2, 0 | 4, 0 => 4
  | _, _ => 0

def op (x y : Fin 35) : Fin 35 :=
  let a := (2 * (x.1 / 5) + y.1 / 5) % 7
  let b := (4 * (x.1 % 5) + 2 * (y.1 % 5) + h (x.1 / 5) (y.1 / 5)) % 5
  ⟨5 * a + b, by
    have ha : a < 7 := Nat.mod_lt _ (by decide)
    have hb : b < 5 := Nat.mod_lt _ (by decide)
    omega⟩

instance magma35 : Magma (Fin 35) := ⟨op⟩

theorem source : EquationLHS (Fin 35) := by decideFin!

theorem target_false : ¬ EquationRHS (Fin 35) := by
  intro q
  have bad := congrArg Fin.val (q 5 20)
  norm_num [Magma.op, op, h] at bad

end submission

def submission : Goal :=
  ⟨Fin 35, submission.magma35, submission.source, submission.target_false⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_11051_to_10201 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_11051_to_10201
