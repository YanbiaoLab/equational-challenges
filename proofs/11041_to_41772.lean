-- Equation11041 → Equation41772
-- Recorded verdict: false
-- Premise: x = y ◇ ((x ◇ (x ◇ x)) ◇ (y ◇ y))
-- Conclusion: x ◇ y = x ◇ (y ◇ (x ◇ (y ◇ x)))
-- Original submission SHA-256: 6b15d4f44d92212476b0ea9e26c0b648004b226331ab3d4e828def9fba6bc9cb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ ((x ◇ (x ◇ x)) ◇ (y ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = x ◇ (y ◇ (x ◇ (y ◇ x)))
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
  let m : Magma (Fin 13) := {
    op := fun i j =>
      match i.val, j.val with
      | 0, 0 => (1 : Fin 13)
      | 0, 1 => (5 : Fin 13)
      | 0, 2 => (9 : Fin 13)
      | 0, 3 => (0 : Fin 13)
      | 0, 4 => (4 : Fin 13)
      | 0, 5 => (8 : Fin 13)
      | 0, 6 => (12 : Fin 13)
      | 0, 7 => (3 : Fin 13)
      | 0, 8 => (7 : Fin 13)
      | 0, 9 => (11 : Fin 13)
      | 0, 10 => (2 : Fin 13)
      | 0, 11 => (6 : Fin 13)
      | 0, 12 => (10 : Fin 13)
      | 1, 0 => (11 : Fin 13)
      | 1, 1 => (2 : Fin 13)
      | 1, 2 => (6 : Fin 13)
      | 1, 3 => (10 : Fin 13)
      | 1, 4 => (1 : Fin 13)
      | 1, 5 => (5 : Fin 13)
      | 1, 6 => (9 : Fin 13)
      | 1, 7 => (0 : Fin 13)
      | 1, 8 => (4 : Fin 13)
      | 1, 9 => (8 : Fin 13)
      | 1, 10 => (12 : Fin 13)
      | 1, 11 => (3 : Fin 13)
      | 1, 12 => (7 : Fin 13)
      | 2, 0 => (8 : Fin 13)
      | 2, 1 => (12 : Fin 13)
      | 2, 2 => (3 : Fin 13)
      | 2, 3 => (7 : Fin 13)
      | 2, 4 => (11 : Fin 13)
      | 2, 5 => (2 : Fin 13)
      | 2, 6 => (6 : Fin 13)
      | 2, 7 => (10 : Fin 13)
      | 2, 8 => (1 : Fin 13)
      | 2, 9 => (5 : Fin 13)
      | 2, 10 => (9 : Fin 13)
      | 2, 11 => (0 : Fin 13)
      | 2, 12 => (4 : Fin 13)
      | 3, 0 => (5 : Fin 13)
      | 3, 1 => (9 : Fin 13)
      | 3, 2 => (0 : Fin 13)
      | 3, 3 => (4 : Fin 13)
      | 3, 4 => (8 : Fin 13)
      | 3, 5 => (12 : Fin 13)
      | 3, 6 => (3 : Fin 13)
      | 3, 7 => (7 : Fin 13)
      | 3, 8 => (11 : Fin 13)
      | 3, 9 => (2 : Fin 13)
      | 3, 10 => (6 : Fin 13)
      | 3, 11 => (10 : Fin 13)
      | 3, 12 => (1 : Fin 13)
      | 4, 0 => (2 : Fin 13)
      | 4, 1 => (6 : Fin 13)
      | 4, 2 => (10 : Fin 13)
      | 4, 3 => (1 : Fin 13)
      | 4, 4 => (5 : Fin 13)
      | 4, 5 => (9 : Fin 13)
      | 4, 6 => (0 : Fin 13)
      | 4, 7 => (4 : Fin 13)
      | 4, 8 => (8 : Fin 13)
      | 4, 9 => (12 : Fin 13)
      | 4, 10 => (3 : Fin 13)
      | 4, 11 => (7 : Fin 13)
      | 4, 12 => (11 : Fin 13)
      | 5, 0 => (12 : Fin 13)
      | 5, 1 => (3 : Fin 13)
      | 5, 2 => (7 : Fin 13)
      | 5, 3 => (11 : Fin 13)
      | 5, 4 => (2 : Fin 13)
      | 5, 5 => (6 : Fin 13)
      | 5, 6 => (10 : Fin 13)
      | 5, 7 => (1 : Fin 13)
      | 5, 8 => (5 : Fin 13)
      | 5, 9 => (9 : Fin 13)
      | 5, 10 => (0 : Fin 13)
      | 5, 11 => (4 : Fin 13)
      | 5, 12 => (8 : Fin 13)
      | 6, 0 => (9 : Fin 13)
      | 6, 1 => (0 : Fin 13)
      | 6, 2 => (4 : Fin 13)
      | 6, 3 => (8 : Fin 13)
      | 6, 4 => (12 : Fin 13)
      | 6, 5 => (3 : Fin 13)
      | 6, 6 => (7 : Fin 13)
      | 6, 7 => (11 : Fin 13)
      | 6, 8 => (2 : Fin 13)
      | 6, 9 => (6 : Fin 13)
      | 6, 10 => (10 : Fin 13)
      | 6, 11 => (1 : Fin 13)
      | 6, 12 => (5 : Fin 13)
      | 7, 0 => (6 : Fin 13)
      | 7, 1 => (10 : Fin 13)
      | 7, 2 => (1 : Fin 13)
      | 7, 3 => (5 : Fin 13)
      | 7, 4 => (9 : Fin 13)
      | 7, 5 => (0 : Fin 13)
      | 7, 6 => (4 : Fin 13)
      | 7, 7 => (8 : Fin 13)
      | 7, 8 => (12 : Fin 13)
      | 7, 9 => (3 : Fin 13)
      | 7, 10 => (7 : Fin 13)
      | 7, 11 => (11 : Fin 13)
      | 7, 12 => (2 : Fin 13)
      | 8, 0 => (3 : Fin 13)
      | 8, 1 => (7 : Fin 13)
      | 8, 2 => (11 : Fin 13)
      | 8, 3 => (2 : Fin 13)
      | 8, 4 => (6 : Fin 13)
      | 8, 5 => (10 : Fin 13)
      | 8, 6 => (1 : Fin 13)
      | 8, 7 => (5 : Fin 13)
      | 8, 8 => (9 : Fin 13)
      | 8, 9 => (0 : Fin 13)
      | 8, 10 => (4 : Fin 13)
      | 8, 11 => (8 : Fin 13)
      | 8, 12 => (12 : Fin 13)
      | 9, 0 => (0 : Fin 13)
      | 9, 1 => (4 : Fin 13)
      | 9, 2 => (8 : Fin 13)
      | 9, 3 => (12 : Fin 13)
      | 9, 4 => (3 : Fin 13)
      | 9, 5 => (7 : Fin 13)
      | 9, 6 => (11 : Fin 13)
      | 9, 7 => (2 : Fin 13)
      | 9, 8 => (6 : Fin 13)
      | 9, 9 => (10 : Fin 13)
      | 9, 10 => (1 : Fin 13)
      | 9, 11 => (5 : Fin 13)
      | 9, 12 => (9 : Fin 13)
      | 10, 0 => (10 : Fin 13)
      | 10, 1 => (1 : Fin 13)
      | 10, 2 => (5 : Fin 13)
      | 10, 3 => (9 : Fin 13)
      | 10, 4 => (0 : Fin 13)
      | 10, 5 => (4 : Fin 13)
      | 10, 6 => (8 : Fin 13)
      | 10, 7 => (12 : Fin 13)
      | 10, 8 => (3 : Fin 13)
      | 10, 9 => (7 : Fin 13)
      | 10, 10 => (11 : Fin 13)
      | 10, 11 => (2 : Fin 13)
      | 10, 12 => (6 : Fin 13)
      | 11, 0 => (7 : Fin 13)
      | 11, 1 => (11 : Fin 13)
      | 11, 2 => (2 : Fin 13)
      | 11, 3 => (6 : Fin 13)
      | 11, 4 => (10 : Fin 13)
      | 11, 5 => (1 : Fin 13)
      | 11, 6 => (5 : Fin 13)
      | 11, 7 => (9 : Fin 13)
      | 11, 8 => (0 : Fin 13)
      | 11, 9 => (4 : Fin 13)
      | 11, 10 => (8 : Fin 13)
      | 11, 11 => (12 : Fin 13)
      | 11, 12 => (3 : Fin 13)
      | 12, 0 => (4 : Fin 13)
      | 12, 1 => (8 : Fin 13)
      | 12, 2 => (12 : Fin 13)
      | 12, 3 => (3 : Fin 13)
      | 12, 4 => (7 : Fin 13)
      | 12, 5 => (11 : Fin 13)
      | 12, 6 => (2 : Fin 13)
      | 12, 7 => (6 : Fin 13)
      | 12, 8 => (10 : Fin 13)
      | 12, 9 => (1 : Fin 13)
      | 12, 10 => (5 : Fin 13)
      | 12, 11 => (9 : Fin 13)
      | 12, 12 => (0 : Fin 13)
      | _, _ => (0 : Fin 13)
  }
  refine ⟨Fin 13, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_11041_to_41772 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_11041_to_41772
