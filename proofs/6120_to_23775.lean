-- Equation6120 → Equation23775
-- Recorded verdict: false
-- Premise: x = y ◇ (z ◇ (x ◇ ((z ◇ z) ◇ y)))
-- Conclusion: x = ((y ◇ z) ◇ z) ◇ (x ◇ (y ◇ x))
-- Original submission SHA-256: 818024c98c9985348785045d71ff74ce9c1dc89afa737c9c26cd5ed1b7440ebf
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ (x ◇ ((z ◇ z) ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ z) ◇ (x ◇ (y ◇ x))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   
                              
                                 

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace submission

@[ext] structure G where
  c0 : ZMod 5
  c1 : ZMod 5

namespace G

def op (x y : G) : G :=
  ⟨3 * x.c0 + 4 * x.c1 + 4 * y.c0 + 2 * y.c1,
   2 * x.c0 + 3 * x.c1 + y.c0 + 4 * y.c1⟩

instance instMagma : Magma G where
  op := op

lemma source_holds : EquationLHS G := by
  intro x y z
  change x =
    op (y) (op (z) (op (x) (op (op (z) (z)) (y))))
  rcases x with ⟨x0, x1⟩
  rcases y with ⟨y0, y1⟩
  rcases z with ⟨z0, z1⟩
  apply G.ext <;> simp [op] <;> ring_nf <;>
    simp [show (60 : ZMod 5) = 0 by decide,
          show (86 : ZMod 5) = 1 by decide,
          show (120 : ZMod 5) = 0 by decide,
          show (290 : ZMod 5) = 0 by decide,
          show (455 : ZMod 5) = 0 by decide,
          show (580 : ZMod 5) = 0 by decide,
          show (3685 : ZMod 5) = 0 by decide,
          show (5220 : ZMod 5) = 0 by decide,
          show (7370 : ZMod 5) = 0 by decide]

lemma target_fails : ¬ EquationRHS G := by
  intro target
  have bad :=
    target
      (⟨0, 0⟩ : G)
      (⟨0, 0⟩ : G)
      (⟨1, 0⟩ : G)
  have bad_coordinate := congrArg G.c0 bad
  change (0 : ZMod 5) =
    (3 : ZMod 5) at bad_coordinate
  exact
    (by decide :
      (0 : ZMod 5) ≠
        (3 : ZMod 5)) bad_coordinate

end G

def certificate : Goal :=
  ⟨G, G.instMagma, G.source_holds, G.target_fails⟩

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6120_to_23775 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_6120_to_23775
