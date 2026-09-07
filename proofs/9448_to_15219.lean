-- Equation9448 → Equation15219
-- Recorded verdict: false
-- Premise: x = y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))
-- Conclusion: x = x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ x)
-- Original submission SHA-256: 5f424a006931bd0df7a23a0e9ce4f4ffa62dcd454a578da0ea2f276f8b113211
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ ((y ◇ x) ◇ (y ◇ (y ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ x)
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

abbrev F := ZMod 11
abbrev K := ZMod 7
abbrev G := F × K

def h (a c : F) : K :=
  match a.val, c.val with
  | 0, 0 => 0
  | 0, 1 => 2
  | 0, 2 => 1
  | 0, 3 => 4
  | 0, 4 => 5
  | 0, 5 => 0
  | 0, 6 => 6
  | 0, 7 => 3
  | 0, 8 => 3
  | 0, 9 => 0
  | 0, 10 => 5
  | 1, 0 => 5
  | 1, 1 => 3
  | 1, 2 => 0
  | 1, 3 => 5
  | 1, 4 => 1
  | 1, 5 => 0
  | 1, 6 => 4
  | 1, 7 => 0
  | 1, 8 => 2
  | 1, 9 => 2
  | 1, 10 => 5
  | 2, 0 => 5
  | 2, 1 => 5
  | 2, 2 => 4
  | 2, 3 => 5
  | 2, 4 => 2
  | 2, 5 => 0
  | 2, 6 => 6
  | 2, 7 => 1
  | 2, 8 => 3
  | 2, 9 => 0
  | 2, 10 => 4
  | 3, 0 => 0
  | 3, 1 => 3
  | 3, 2 => 0
  | 3, 3 => 2
  | 3, 4 => 2
  | 3, 5 => 0
  | 3, 6 => 4
  | 3, 7 => 1
  | 3, 8 => 0
  | 3, 9 => 1
  | 3, 10 => 1
  | 4, 0 => 5
  | 4, 1 => 1
  | 4, 2 => 5
  | 4, 3 => 2
  | 4, 4 => 4
  | 4, 5 => 0
  | 4, 6 => 1
  | 4, 7 => 6
  | 4, 8 => 1
  | 4, 9 => 4
  | 4, 10 => 5
  | 5, 0 => 4
  | 5, 1 => 5
  | 5, 2 => 4
  | 5, 3 => 4
  | 5, 4 => 0
  | 5, 5 => 0
  | 5, 6 => 6
  | 5, 7 => 6
  | 5, 8 => 3
  | 5, 9 => 2
  | 5, 10 => 1
  | 6, 0 => 6
  | 6, 1 => 4
  | 6, 2 => 2
  | 6, 3 => 6
  | 6, 4 => 1
  | 6, 5 => 0
  | 6, 6 => 2
  | 6, 7 => 0
  | 6, 8 => 6
  | 6, 9 => 3
  | 6, 10 => 1
  | 7, 0 => 2
  | 7, 1 => 3
  | 7, 2 => 5
  | 7, 3 => 1
  | 7, 4 => 6
  | 7, 5 => 0
  | 7, 6 => 5
  | 7, 7 => 2
  | 7, 8 => 2
  | 7, 9 => 1
  | 7, 10 => 5
  | 8, 0 => 5
  | 8, 1 => 5
  | 8, 2 => 3
  | 8, 3 => 1
  | 8, 4 => 1
  | 8, 5 => 0
  | 8, 6 => 3
  | 8, 7 => 5
  | 8, 8 => 6
  | 8, 9 => 3
  | 8, 10 => 1
  | 9, 0 => 4
  | 9, 1 => 3
  | 9, 2 => 4
  | 9, 3 => 5
  | 9, 4 => 5
  | 9, 5 => 0
  | 9, 6 => 1
  | 9, 7 => 1
  | 9, 8 => 0
  | 9, 9 => 5
  | _, _ => 0

def op (x y : G) : G :=
  (9 * x.1 + 4 * y.1, 4 * x.2 + 4 * y.2 + h x.1 y.1)

instance magmaG : Magma G := ⟨op⟩

theorem source : EquationLHS G := by
  decideFin!

theorem target_false : ¬ EquationRHS G := by
  intro q
  have bad : ((1, 0) : G) ≠
      (1, 0) ◇ ((((1, 0) ◇ ((1, 0) ◇ (1, 0))) ◇ (1, 0)) ◇ (1, 0)) := by
    decide
  exact bad (q (1, 0))

end submission

def submission : Goal :=
  ⟨submission.G, submission.magmaG, submission.source, submission.target_false⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_9448_to_15219 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_9448_to_15219
