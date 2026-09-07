-- Equation9543 → Equation10104
-- Recorded verdict: false
-- Premise: x = y * ((y * z) * (z * (x * y)))
-- Conclusion: x = x * ((y * z) * ((y * y) * x))
-- Original submission SHA-256: 70fe01e326532252c6cba7d620f4cb9ca74244520964631005f4d28cf1a9fa69
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((y ◇ z) ◇ (z ◇ (x ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ ((y ◇ z) ◇ ((y ◇ y) ◇ x))
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

namespace G

def op (x y : G) : G :=
  ⟨x.c1 + y.c0 + y.c1,
   x.c1 + x.c2 + y.c2,
   x.c2 + x.c3 + y.c3,
   x.c0 + x.c3 + y.c0⟩

instance instMagma : Magma G where
  op := op

lemma source_holds : EquationLHS G := by
  intro x y z
  change x =
    op (y) (op (op (y) (z)) (op (z) (op (x) (y))))
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  rcases z with ⟨z0, z1, z2, z3⟩
  apply G.ext <;> simp [op] <;> ring_nf <;>
    simp [show (2 : ZMod 2) = 0 by decide,
          show (4 : ZMod 2) = 0 by decide]

lemma target_fails : ¬ EquationRHS G := by
  intro target
  have bad :=
    target
      (⟨0, 0, 0, 0⟩ : G)
      (⟨0, 0, 0, 0⟩ : G)
      (⟨1, 0, 0, 0⟩ : G)
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
theorem certificate_9543_to_10104 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_9543_to_10104
