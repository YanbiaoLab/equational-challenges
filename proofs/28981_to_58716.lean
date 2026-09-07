-- Equation28981 → Equation58716
-- Recorded verdict: false
-- Premise: x = (((y ◇ z) ◇ y) ◇ y) ◇ (z ◇ x)
-- Conclusion: (x ◇ y) ◇ z = x ◇ (y ◇ (x ◇ z))
-- Original submission SHA-256: 0e264cc3aac7f017e0553977a06febdafe6dfe6068fd9666b7e34db3d86617be
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((y ◇ z) ◇ y) ◇ y) ◇ (z ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = x ◇ (y ◇ (x ◇ z))
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
      | 0, 0 => (0 : Fin 10)
      | 0, 1 => (2 : Fin 10)
      | 0, 2 => (1 : Fin 10)
      | 0, 3 => (4 : Fin 10)
      | 0, 4 => (3 : Fin 10)
      | 0, 5 => (6 : Fin 10)
      | 0, 6 => (5 : Fin 10)
      | 0, 7 => (9 : Fin 10)
      | 0, 8 => (8 : Fin 10)
      | 0, 9 => (7 : Fin 10)
      | 1, 0 => (3 : Fin 10)
      | 1, 1 => (1 : Fin 10)
      | 1, 2 => (4 : Fin 10)
      | 1, 3 => (0 : Fin 10)
      | 1, 4 => (2 : Fin 10)
      | 1, 5 => (7 : Fin 10)
      | 1, 6 => (8 : Fin 10)
      | 1, 7 => (5 : Fin 10)
      | 1, 8 => (6 : Fin 10)
      | 1, 9 => (9 : Fin 10)
      | 2, 0 => (5 : Fin 10)
      | 2, 1 => (3 : Fin 10)
      | 2, 2 => (2 : Fin 10)
      | 2, 3 => (1 : Fin 10)
      | 2, 4 => (8 : Fin 10)
      | 2, 5 => (0 : Fin 10)
      | 2, 6 => (9 : Fin 10)
      | 2, 7 => (7 : Fin 10)
      | 2, 8 => (4 : Fin 10)
      | 2, 9 => (6 : Fin 10)
      | 3, 0 => (2 : Fin 10)
      | 3, 1 => (4 : Fin 10)
      | 3, 2 => (0 : Fin 10)
      | 3, 3 => (3 : Fin 10)
      | 3, 4 => (1 : Fin 10)
      | 3, 5 => (9 : Fin 10)
      | 3, 6 => (6 : Fin 10)
      | 3, 7 => (8 : Fin 10)
      | 3, 8 => (7 : Fin 10)
      | 3, 9 => (5 : Fin 10)
      | 4, 0 => (1 : Fin 10)
      | 4, 1 => (0 : Fin 10)
      | 4, 2 => (3 : Fin 10)
      | 4, 3 => (2 : Fin 10)
      | 4, 4 => (4 : Fin 10)
      | 4, 5 => (5 : Fin 10)
      | 4, 6 => (7 : Fin 10)
      | 4, 7 => (6 : Fin 10)
      | 4, 8 => (9 : Fin 10)
      | 4, 9 => (8 : Fin 10)
      | 5, 0 => (1 : Fin 10)
      | 5, 1 => (0 : Fin 10)
      | 5, 2 => (3 : Fin 10)
      | 5, 3 => (2 : Fin 10)
      | 5, 4 => (4 : Fin 10)
      | 5, 5 => (5 : Fin 10)
      | 5, 6 => (7 : Fin 10)
      | 5, 7 => (6 : Fin 10)
      | 5, 8 => (9 : Fin 10)
      | 5, 9 => (8 : Fin 10)
      | 6, 0 => (2 : Fin 10)
      | 6, 1 => (4 : Fin 10)
      | 6, 2 => (0 : Fin 10)
      | 6, 3 => (3 : Fin 10)
      | 6, 4 => (1 : Fin 10)
      | 6, 5 => (9 : Fin 10)
      | 6, 6 => (6 : Fin 10)
      | 6, 7 => (8 : Fin 10)
      | 6, 8 => (7 : Fin 10)
      | 6, 9 => (5 : Fin 10)
      | 7, 0 => (5 : Fin 10)
      | 7, 1 => (3 : Fin 10)
      | 7, 2 => (2 : Fin 10)
      | 7, 3 => (1 : Fin 10)
      | 7, 4 => (8 : Fin 10)
      | 7, 5 => (0 : Fin 10)
      | 7, 6 => (9 : Fin 10)
      | 7, 7 => (7 : Fin 10)
      | 7, 8 => (4 : Fin 10)
      | 7, 9 => (6 : Fin 10)
      | 8, 0 => (0 : Fin 10)
      | 8, 1 => (2 : Fin 10)
      | 8, 2 => (1 : Fin 10)
      | 8, 3 => (4 : Fin 10)
      | 8, 4 => (3 : Fin 10)
      | 8, 5 => (6 : Fin 10)
      | 8, 6 => (5 : Fin 10)
      | 8, 7 => (9 : Fin 10)
      | 8, 8 => (8 : Fin 10)
      | 8, 9 => (7 : Fin 10)
      | 9, 0 => (3 : Fin 10)
      | 9, 1 => (1 : Fin 10)
      | 9, 2 => (4 : Fin 10)
      | 9, 3 => (0 : Fin 10)
      | 9, 4 => (2 : Fin 10)
      | 9, 5 => (7 : Fin 10)
      | 9, 6 => (8 : Fin 10)
      | 9, 7 => (5 : Fin 10)
      | 9, 8 => (6 : Fin 10)
      | 9, 9 => (9 : Fin 10)
      | _, _ => (0 : Fin 10)
  }
  refine ⟨Fin 10, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_28981_to_58716 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_28981_to_58716
