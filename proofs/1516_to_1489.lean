-- Equation1516 → Equation1489
-- Recorded verdict: false
-- Premise: x = (y ◇ y) ◇ (x ◇ (x ◇ y))
-- Conclusion: x = (y ◇ x) ◇ (y ◇ (x ◇ y))
-- Original submission SHA-256: 26b2a1c30ca7fa8ff900fc92db215962829fc02e96812850ea371af50ff7f6a1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ y) ◇ (x ◇ (x ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ x) ◇ (y ◇ (x ◇ y))
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
  | 0, 0 => 1 | 0, 1 => 0 | 0, 2 => 4 | 0, 3 => 1 | 0, _ => 3
  | 1, 0 => 0 | 1, 1 => 0 | 1, 2 => 2 | 1, 3 => 6 | 1, _ => 6
  | 2, 0 => 0 | 2, 1 => 0 | 2, 2 => 5 | 2, 3 => 4 | 2, _ => 1
  | 3, 0 => 0 | 3, 1 => 0 | 3, 2 => 0 | 3, 3 => 6 | 3, _ => 3
  | _, 0 => 0 | _, 1 => 5 | _, 2 => 2 | _, 3 => 6 | _, _ => 4

def op (x y : Fin 35) : Fin 35 :=
  let a := (3 * (x.1 / 7 + y.1 / 7)) % 5
  let b := (y.1 % 7 + 4 * (x.1 % 7) + h (x.1 / 7) (y.1 / 7)) % 7
  ⟨7 * a + b, by
    have ha : a < 5 := Nat.mod_lt _ (by decide)
    have hb : b < 7 := Nat.mod_lt _ (by decide)
    omega⟩

instance magma35 : Magma (Fin 35) := ⟨op⟩

theorem source : EquationLHS (Fin 35) := by decideFin!

theorem target_false : ¬ EquationRHS (Fin 35) := by
  intro q
  have bad := q 0 7
  norm_num [Magma.op, op, h] at bad

end submission

def submission : Goal :=
  ⟨Fin 35, submission.magma35, submission.source, submission.target_false⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1516_to_1489 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_1516_to_1489
