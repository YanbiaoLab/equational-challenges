-- Equation54033 → Equation54014
-- Recorded verdict: false
-- Premise: x ◇ (y ◇ x) = x ◇ (z ◇ (x ◇ w))
-- Conclusion: x ◇ (y ◇ x) = x ◇ (x ◇ (y ◇ y))
-- Original submission SHA-256: ae710bb8a2ba62037b1dd10ab60e7eed87c7189b8596d05d9506059f225123e1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ x) = x ◇ (z ◇ (x ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (y ◇ x) = x ◇ (x ◇ (y ◇ y))
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

def submission : Goal := by
  let m : Magma (Fin 10) := {
    op := fun i j =>
      match i.val, j.val with
      | 0, 0 => (7 : Fin 10)
      | 0, 1 => (7 : Fin 10)
      | 0, 2 => (5 : Fin 10)
      | 0, 3 => (5 : Fin 10)
      | 0, 4 => (5 : Fin 10)
      | 0, 5 => (5 : Fin 10)
      | 0, 6 => (5 : Fin 10)
      | 0, 7 => (5 : Fin 10)
      | 0, 8 => (2 : Fin 10)
      | 0, 9 => (2 : Fin 10)
      | 1, 0 => (6 : Fin 10)
      | 1, 1 => (6 : Fin 10)
      | 1, 2 => (5 : Fin 10)
      | 1, 3 => (5 : Fin 10)
      | 1, 4 => (5 : Fin 10)
      | 1, 5 => (5 : Fin 10)
      | 1, 6 => (5 : Fin 10)
      | 1, 7 => (5 : Fin 10)
      | 1, 8 => (2 : Fin 10)
      | 1, 9 => (3 : Fin 10)
      | 2, 0 => (5 : Fin 10)
      | 2, 1 => (5 : Fin 10)
      | 2, 2 => (5 : Fin 10)
      | 2, 3 => (5 : Fin 10)
      | 2, 4 => (5 : Fin 10)
      | 2, 5 => (5 : Fin 10)
      | 2, 6 => (3 : Fin 10)
      | 2, 7 => (3 : Fin 10)
      | 2, 8 => (5 : Fin 10)
      | 2, 9 => (5 : Fin 10)
      | 3, 0 => (5 : Fin 10)
      | 3, 1 => (5 : Fin 10)
      | 3, 2 => (4 : Fin 10)
      | 3, 3 => (4 : Fin 10)
      | 3, 4 => (5 : Fin 10)
      | 3, 5 => (5 : Fin 10)
      | 3, 6 => (3 : Fin 10)
      | 3, 7 => (3 : Fin 10)
      | 3, 8 => (5 : Fin 10)
      | 3, 9 => (5 : Fin 10)
      | 4, 0 => (5 : Fin 10)
      | 4, 1 => (5 : Fin 10)
      | 4, 2 => (5 : Fin 10)
      | 4, 3 => (5 : Fin 10)
      | 4, 4 => (5 : Fin 10)
      | 4, 5 => (5 : Fin 10)
      | 4, 6 => (5 : Fin 10)
      | 4, 7 => (5 : Fin 10)
      | 4, 8 => (2 : Fin 10)
      | 4, 9 => (2 : Fin 10)
      | 5, 0 => (5 : Fin 10)
      | 5, 1 => (5 : Fin 10)
      | 5, 2 => (5 : Fin 10)
      | 5, 3 => (5 : Fin 10)
      | 5, 4 => (5 : Fin 10)
      | 5, 5 => (5 : Fin 10)
      | 5, 6 => (5 : Fin 10)
      | 5, 7 => (5 : Fin 10)
      | 5, 8 => (2 : Fin 10)
      | 5, 9 => (3 : Fin 10)
      | 6, 0 => (5 : Fin 10)
      | 6, 1 => (5 : Fin 10)
      | 6, 2 => (5 : Fin 10)
      | 6, 3 => (5 : Fin 10)
      | 6, 4 => (5 : Fin 10)
      | 6, 5 => (5 : Fin 10)
      | 6, 6 => (5 : Fin 10)
      | 6, 7 => (5 : Fin 10)
      | 6, 8 => (5 : Fin 10)
      | 6, 9 => (5 : Fin 10)
      | 7, 0 => (5 : Fin 10)
      | 7, 1 => (5 : Fin 10)
      | 7, 2 => (5 : Fin 10)
      | 7, 3 => (5 : Fin 10)
      | 7, 4 => (5 : Fin 10)
      | 7, 5 => (5 : Fin 10)
      | 7, 6 => (4 : Fin 10)
      | 7, 7 => (4 : Fin 10)
      | 7, 8 => (5 : Fin 10)
      | 7, 9 => (5 : Fin 10)
      | 8, 0 => (5 : Fin 10)
      | 8, 1 => (5 : Fin 10)
      | 8, 2 => (5 : Fin 10)
      | 8, 3 => (5 : Fin 10)
      | 8, 4 => (5 : Fin 10)
      | 8, 5 => (5 : Fin 10)
      | 8, 6 => (5 : Fin 10)
      | 8, 7 => (5 : Fin 10)
      | 8, 8 => (3 : Fin 10)
      | 8, 9 => (3 : Fin 10)
      | 9, 0 => (5 : Fin 10)
      | 9, 1 => (5 : Fin 10)
      | 9, 2 => (5 : Fin 10)
      | 9, 3 => (5 : Fin 10)
      | 9, 4 => (5 : Fin 10)
      | 9, 5 => (5 : Fin 10)
      | 9, 6 => (5 : Fin 10)
      | 9, 7 => (5 : Fin 10)
      | 9, 8 => (2 : Fin 10)
      | 9, 9 => (2 : Fin 10)
      | _, _ => (0 : Fin 10)
  }
  refine ⟨Fin 10, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_54033_to_54014 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_54033_to_54014
