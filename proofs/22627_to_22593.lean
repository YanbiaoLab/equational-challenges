-- Equation22627 → Equation22593
-- Recorded verdict: false
-- Premise: x = (y ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ y)
-- Conclusion: x = (y ◇ (y ◇ x)) ◇ ((x ◇ y) ◇ y)
-- Original submission SHA-256: 1729d1f74137ac86459cd20d9183131859a61936641d80a472aa27d97ba338e1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ (y ◇ x)) ◇ ((x ◇ y) ◇ y)
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
  let m : Magma (Fin 12) := {
    op := fun i j =>
      match i.val, j.val with
      | 0, 0 => (11 : Fin 12)
      | 0, 1 => (2 : Fin 12)
      | 0, 2 => (5 : Fin 12)
      | 0, 3 => (0 : Fin 12)
      | 0, 4 => (10 : Fin 12)
      | 0, 5 => (9 : Fin 12)
      | 0, 6 => (4 : Fin 12)
      | 0, 7 => (6 : Fin 12)
      | 0, 8 => (8 : Fin 12)
      | 0, 9 => (1 : Fin 12)
      | 0, 10 => (7 : Fin 12)
      | 0, 11 => (3 : Fin 12)
      | 1, 0 => (7 : Fin 12)
      | 1, 1 => (5 : Fin 12)
      | 1, 2 => (0 : Fin 12)
      | 1, 3 => (2 : Fin 12)
      | 1, 4 => (11 : Fin 12)
      | 1, 5 => (6 : Fin 12)
      | 1, 6 => (1 : Fin 12)
      | 1, 7 => (3 : Fin 12)
      | 1, 8 => (4 : Fin 12)
      | 1, 9 => (8 : Fin 12)
      | 1, 10 => (10 : Fin 12)
      | 1, 11 => (9 : Fin 12)
      | 2, 0 => (1 : Fin 12)
      | 2, 1 => (11 : Fin 12)
      | 2, 2 => (7 : Fin 12)
      | 2, 3 => (10 : Fin 12)
      | 2, 4 => (4 : Fin 12)
      | 2, 5 => (3 : Fin 12)
      | 2, 6 => (0 : Fin 12)
      | 2, 7 => (9 : Fin 12)
      | 2, 8 => (5 : Fin 12)
      | 2, 9 => (2 : Fin 12)
      | 2, 10 => (8 : Fin 12)
      | 2, 11 => (6 : Fin 12)
      | 3, 0 => (3 : Fin 12)
      | 3, 1 => (7 : Fin 12)
      | 3, 2 => (6 : Fin 12)
      | 3, 3 => (8 : Fin 12)
      | 3, 4 => (1 : Fin 12)
      | 3, 5 => (4 : Fin 12)
      | 3, 6 => (9 : Fin 12)
      | 3, 7 => (5 : Fin 12)
      | 3, 8 => (0 : Fin 12)
      | 3, 9 => (10 : Fin 12)
      | 3, 10 => (2 : Fin 12)
      | 3, 11 => (11 : Fin 12)
      | 4, 0 => (6 : Fin 12)
      | 4, 1 => (0 : Fin 12)
      | 4, 2 => (2 : Fin 12)
      | 4, 3 => (5 : Fin 12)
      | 4, 4 => (9 : Fin 12)
      | 4, 5 => (8 : Fin 12)
      | 4, 6 => (11 : Fin 12)
      | 4, 7 => (4 : Fin 12)
      | 4, 8 => (10 : Fin 12)
      | 4, 9 => (7 : Fin 12)
      | 4, 10 => (3 : Fin 12)
      | 4, 11 => (1 : Fin 12)
      | 5, 0 => (4 : Fin 12)
      | 5, 1 => (10 : Fin 12)
      | 5, 2 => (8 : Fin 12)
      | 5, 3 => (9 : Fin 12)
      | 5, 4 => (3 : Fin 12)
      | 5, 5 => (1 : Fin 12)
      | 5, 6 => (6 : Fin 12)
      | 5, 7 => (11 : Fin 12)
      | 5, 8 => (7 : Fin 12)
      | 5, 9 => (0 : Fin 12)
      | 5, 10 => (5 : Fin 12)
      | 5, 11 => (2 : Fin 12)
      | 6, 0 => (9 : Fin 12)
      | 6, 1 => (6 : Fin 12)
      | 6, 2 => (11 : Fin 12)
      | 6, 3 => (4 : Fin 12)
      | 6, 4 => (0 : Fin 12)
      | 6, 5 => (5 : Fin 12)
      | 6, 6 => (10 : Fin 12)
      | 6, 7 => (8 : Fin 12)
      | 6, 8 => (2 : Fin 12)
      | 6, 9 => (3 : Fin 12)
      | 6, 10 => (1 : Fin 12)
      | 6, 11 => (7 : Fin 12)
      | 7, 0 => (10 : Fin 12)
      | 7, 1 => (8 : Fin 12)
      | 7, 2 => (4 : Fin 12)
      | 7, 3 => (1 : Fin 12)
      | 7, 4 => (7 : Fin 12)
      | 7, 5 => (0 : Fin 12)
      | 7, 6 => (3 : Fin 12)
      | 7, 7 => (2 : Fin 12)
      | 7, 8 => (6 : Fin 12)
      | 7, 9 => (9 : Fin 12)
      | 7, 10 => (11 : Fin 12)
      | 7, 11 => (5 : Fin 12)
      | 8, 0 => (0 : Fin 12)
      | 8, 1 => (9 : Fin 12)
      | 8, 2 => (1 : Fin 12)
      | 8, 3 => (11 : Fin 12)
      | 8, 4 => (6 : Fin 12)
      | 8, 5 => (2 : Fin 12)
      | 8, 6 => (7 : Fin 12)
      | 8, 7 => (10 : Fin 12)
      | 8, 8 => (3 : Fin 12)
      | 8, 9 => (5 : Fin 12)
      | 8, 10 => (4 : Fin 12)
      | 8, 11 => (8 : Fin 12)
      | 9, 0 => (5 : Fin 12)
      | 9, 1 => (3 : Fin 12)
      | 9, 2 => (9 : Fin 12)
      | 9, 3 => (6 : Fin 12)
      | 9, 4 => (2 : Fin 12)
      | 9, 5 => (11 : Fin 12)
      | 9, 6 => (8 : Fin 12)
      | 9, 7 => (7 : Fin 12)
      | 9, 8 => (1 : Fin 12)
      | 9, 9 => (4 : Fin 12)
      | 9, 10 => (0 : Fin 12)
      | 9, 11 => (10 : Fin 12)
      | 10, 0 => (2 : Fin 12)
      | 10, 1 => (1 : Fin 12)
      | 10, 2 => (3 : Fin 12)
      | 10, 3 => (7 : Fin 12)
      | 10, 4 => (8 : Fin 12)
      | 10, 5 => (10 : Fin 12)
      | 10, 6 => (5 : Fin 12)
      | 10, 7 => (0 : Fin 12)
      | 10, 8 => (9 : Fin 12)
      | 10, 9 => (11 : Fin 12)
      | 10, 10 => (6 : Fin 12)
      | 10, 11 => (4 : Fin 12)
      | 11, 0 => (8 : Fin 12)
      | 11, 1 => (4 : Fin 12)
      | 11, 2 => (10 : Fin 12)
      | 11, 3 => (3 : Fin 12)
      | 11, 4 => (5 : Fin 12)
      | 11, 5 => (7 : Fin 12)
      | 11, 6 => (2 : Fin 12)
      | 11, 7 => (1 : Fin 12)
      | 11, 8 => (11 : Fin 12)
      | 11, 9 => (6 : Fin 12)
      | 11, 10 => (9 : Fin 12)
      | 11, 11 => (0 : Fin 12)
      | _, _ => (0 : Fin 12)
  }
  refine ⟨Fin 12, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22627_to_22593 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_22627_to_22593
