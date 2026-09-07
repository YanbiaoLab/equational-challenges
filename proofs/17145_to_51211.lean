-- Equation17145 → Equation51211
-- Recorded verdict: false
-- Premise: x = (x ◇ y) ◇ (z ◇ (z ◇ (w ◇ x)))
-- Conclusion: x ◇ x = ((x ◇ y) ◇ (z ◇ x)) ◇ x
-- Original submission SHA-256: e6ab748e24267985a818ea7d880ae1560341375835f7d49a9f8ae2e69aeb129c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ y) ◇ (z ◇ (z ◇ (w ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = ((x ◇ y) ◇ (z ◇ x)) ◇ x
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
      | 0, 2 => (2 : Fin 10)
      | 0, 3 => (2 : Fin 10)
      | 0, 4 => (8 : Fin 10)
      | 0, 5 => (8 : Fin 10)
      | 0, 6 => (4 : Fin 10)
      | 0, 7 => (4 : Fin 10)
      | 0, 8 => (1 : Fin 10)
      | 0, 9 => (1 : Fin 10)
      | 1, 0 => (6 : Fin 10)
      | 1, 1 => (6 : Fin 10)
      | 1, 2 => (3 : Fin 10)
      | 1, 3 => (3 : Fin 10)
      | 1, 4 => (9 : Fin 10)
      | 1, 5 => (9 : Fin 10)
      | 1, 6 => (5 : Fin 10)
      | 1, 7 => (5 : Fin 10)
      | 1, 8 => (0 : Fin 10)
      | 1, 9 => (0 : Fin 10)
      | 2, 0 => (6 : Fin 10)
      | 2, 1 => (6 : Fin 10)
      | 2, 2 => (2 : Fin 10)
      | 2, 3 => (2 : Fin 10)
      | 2, 4 => (9 : Fin 10)
      | 2, 5 => (9 : Fin 10)
      | 2, 6 => (5 : Fin 10)
      | 2, 7 => (5 : Fin 10)
      | 2, 8 => (0 : Fin 10)
      | 2, 9 => (0 : Fin 10)
      | 3, 0 => (7 : Fin 10)
      | 3, 1 => (7 : Fin 10)
      | 3, 2 => (3 : Fin 10)
      | 3, 3 => (3 : Fin 10)
      | 3, 4 => (8 : Fin 10)
      | 3, 5 => (8 : Fin 10)
      | 3, 6 => (4 : Fin 10)
      | 3, 7 => (4 : Fin 10)
      | 3, 8 => (1 : Fin 10)
      | 3, 9 => (1 : Fin 10)
      | 4, 0 => (7 : Fin 10)
      | 4, 1 => (7 : Fin 10)
      | 4, 2 => (3 : Fin 10)
      | 4, 3 => (3 : Fin 10)
      | 4, 4 => (8 : Fin 10)
      | 4, 5 => (8 : Fin 10)
      | 4, 6 => (4 : Fin 10)
      | 4, 7 => (4 : Fin 10)
      | 4, 8 => (0 : Fin 10)
      | 4, 9 => (0 : Fin 10)
      | 5, 0 => (6 : Fin 10)
      | 5, 1 => (6 : Fin 10)
      | 5, 2 => (2 : Fin 10)
      | 5, 3 => (2 : Fin 10)
      | 5, 4 => (9 : Fin 10)
      | 5, 5 => (9 : Fin 10)
      | 5, 6 => (5 : Fin 10)
      | 5, 7 => (5 : Fin 10)
      | 5, 8 => (1 : Fin 10)
      | 5, 9 => (1 : Fin 10)
      | 6, 0 => (6 : Fin 10)
      | 6, 1 => (6 : Fin 10)
      | 6, 2 => (2 : Fin 10)
      | 6, 3 => (2 : Fin 10)
      | 6, 4 => (8 : Fin 10)
      | 6, 5 => (8 : Fin 10)
      | 6, 6 => (5 : Fin 10)
      | 6, 7 => (5 : Fin 10)
      | 6, 8 => (1 : Fin 10)
      | 6, 9 => (1 : Fin 10)
      | 7, 0 => (7 : Fin 10)
      | 7, 1 => (7 : Fin 10)
      | 7, 2 => (3 : Fin 10)
      | 7, 3 => (3 : Fin 10)
      | 7, 4 => (9 : Fin 10)
      | 7, 5 => (9 : Fin 10)
      | 7, 6 => (4 : Fin 10)
      | 7, 7 => (4 : Fin 10)
      | 7, 8 => (0 : Fin 10)
      | 7, 9 => (0 : Fin 10)
      | 8, 0 => (6 : Fin 10)
      | 8, 1 => (6 : Fin 10)
      | 8, 2 => (3 : Fin 10)
      | 8, 3 => (3 : Fin 10)
      | 8, 4 => (9 : Fin 10)
      | 8, 5 => (9 : Fin 10)
      | 8, 6 => (4 : Fin 10)
      | 8, 7 => (4 : Fin 10)
      | 8, 8 => (0 : Fin 10)
      | 8, 9 => (0 : Fin 10)
      | 9, 0 => (7 : Fin 10)
      | 9, 1 => (7 : Fin 10)
      | 9, 2 => (2 : Fin 10)
      | 9, 3 => (2 : Fin 10)
      | 9, 4 => (8 : Fin 10)
      | 9, 5 => (8 : Fin 10)
      | 9, 6 => (5 : Fin 10)
      | 9, 7 => (5 : Fin 10)
      | 9, 8 => (1 : Fin 10)
      | 9, 9 => (1 : Fin 10)
      | _, _ => (0 : Fin 10)
  }
  refine ⟨Fin 10, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_17145_to_51211 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_17145_to_51211
