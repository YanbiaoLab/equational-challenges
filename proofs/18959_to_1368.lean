-- Equation18959 → Equation1368
-- Recorded verdict: false
-- Premise: x = (y ◇ x) ◇ ((x ◇ z) ◇ (z ◇ y))
-- Conclusion: x = y ◇ (((z ◇ y) ◇ x) ◇ z)
-- Original submission SHA-256: 2c3c61072d4a168422eab137a5a2eeb4c0dc13f596c502eb8e8d7a62e3d84dad
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring.RingNF

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ ((x ◇ z) ◇ (z ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (((z ◇ y) ◇ x) ◇ z)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   
                              
                                 

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace submission

@[ext] structure G where
  c0 : ZMod 2
  c1 : ZMod 2
  c2 : ZMod 2
  c3 : ZMod 2
  c4 : ZMod 2

namespace G

def op (x y : G) : G :=
  ⟨x.c0 + x.c4 + y.c2 + y.c3 + y.c4,
   x.c0 + x.c1 + y.c0 + y.c3 + y.c4,
   x.c1 + x.c2 + x.c4 + y.c0 + y.c1 + y.c2 + y.c3,
   x.c2 + x.c3 + y.c0 + y.c1 + y.c2 + y.c3 + y.c4,
   x.c3 + x.c4 + y.c1 + y.c2 + y.c3 + y.c4⟩

instance instMagma : Magma G where
  op := op

lemma source_holds : EquationLHS G := by
  intro x y z
  change x =
    op (op (y) (x)) (op (op (x) (z)) (op (z) (y)))
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  rcases y with ⟨y0, y1, y2, y3, y4⟩
  rcases z with ⟨z0, z1, z2, z3, z4⟩
  apply G.ext <;> simp [op] <;> ring_nf <;>
    simp [show (2 : ZMod 2) = 0 by decide,
          show (4 : ZMod 2) = 0 by decide,
          show (5 : ZMod 2) = 1 by decide,
          show (6 : ZMod 2) = 0 by decide,
          show (7 : ZMod 2) = 1 by decide,
          show (8 : ZMod 2) = 0 by decide,
          show (10 : ZMod 2) = 0 by decide,
          show (12 : ZMod 2) = 0 by decide,
          show (14 : ZMod 2) = 0 by decide,
          show (16 : ZMod 2) = 0 by decide,
          show (18 : ZMod 2) = 0 by decide,
          show (20 : ZMod 2) = 0 by decide]

lemma target_fails : ¬ EquationRHS G := by
  intro target
  have bad :=
    target
      (⟨0, 0, 0, 0, 0⟩ : G)
      (⟨0, 0, 0, 0, 0⟩ : G)
      (⟨1, 0, 0, 0, 0⟩ : G)
  have bad_coordinate := congrArg G.c1 bad
  change (0 : ZMod 2) =
    (1 : ZMod 2) at bad_coordinate
  exact
    (by decide :
      (0 : ZMod 2) ≠
        (1 : ZMod 2)) bad_coordinate

end G

def certificate : Goal :=
  ⟨G, G.instMagma, G.source_holds, G.target_fails⟩

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_18959_to_1368 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_18959_to_1368
