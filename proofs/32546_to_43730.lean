-- Equation32546 → Equation43730
-- Recorded verdict: false
-- Premise: x = (y * ((z * (z * x)) * y)) * y
-- Conclusion: x * y = y * ((z * y) * (x * z))
-- Original submission SHA-256: 96e8fd75d0e41da1de3e1ddca965cbd6adc4be08e641c7a025c0f024fbcb636a
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ ((z ◇ (z ◇ x)) ◇ y)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ ((z ◇ y) ◇ (x ◇ z))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   
                              
                             
                                 

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace submission

@[ext] structure G where
  a : ZMod 5
  b : ZMod 5
  c : ZMod 5
  d : ZMod 5

namespace G

def q (x : ZMod 5) : ZMod 5 := 3 * x * (x + 1)

def mul (x y : G) : G :=
  ⟨x.a + y.a,
   x.b + y.b + x.a * y.d,
   x.c + y.c + x.a * q y.d + x.b * y.d,
   x.d + y.d⟩

def inv (x : G) : G :=
  ⟨-x.a,
   -x.b + x.a * x.d,
   -x.c + x.a * q x.d + x.b * x.d - x.a * x.d * x.d,
   -x.d⟩

def op (x y : G) : G := mul (mul x (inv y)) x

instance instMagma : Magma G where
  op := op

lemma left_involutive (x y : G) : op x (op x y) = y := by
  rcases x with ⟨xa, xb, xc, xd⟩
  rcases y with ⟨ya, yb, yc, yd⟩
  apply G.ext <;> simp [op, mul, inv, q] <;> ring_nf
  simp [show (5 : ZMod 5) = 0 by decide,
        show (10 : ZMod 5) = 0 by decide,
        show (25 : ZMod 5) = 0 by decide,
        show (30 : ZMod 5) = 0 by decide]

lemma cycle5 (x y : G) : op (op y (op x y)) y = x := by
  rcases x with ⟨xa, xb, xc, xd⟩
  rcases y with ⟨ya, yb, yc, yd⟩
  apply G.ext <;> simp [op, mul, inv, q] <;> ring_nf <;>
    simp [show (4 : ZMod 5) = -1 by decide,
          show (5 : ZMod 5) = 0 by decide,
          show (10 : ZMod 5) = 0 by decide,
          show (30 : ZMod 5) = 0 by decide,
          show (40 : ZMod 5) = 0 by decide,
          show (50 : ZMod 5) = 0 by decide,
          show (70 : ZMod 5) = 0 by decide,
          show (75 : ZMod 5) = 0 by decide,
          show (90 : ZMod 5) = 0 by decide]

lemma source_holds : EquationLHS G := by
  intro x y z
  change x = op (op y (op (op z (op z x)) y)) y
  rw [left_involutive z x]
  exact (cycle5 x y).symm

lemma target_fails : ¬ EquationRHS G := by
  intro target
  have bad := target
    (⟨0, 0, 0, 0⟩ : G)
    (⟨1, 0, 0, 0⟩ : G)
    (⟨0, 0, 0, 1⟩ : G)
  change op (⟨0, 0, 0, 0⟩ : G) (⟨1, 0, 0, 0⟩ : G) =
    op (⟨1, 0, 0, 0⟩ : G)
      (op (op (⟨0, 0, 0, 1⟩ : G) (⟨1, 0, 0, 0⟩ : G))
        (op (⟨0, 0, 0, 0⟩ : G) (⟨0, 0, 0, 1⟩ : G))) at bad
  have hc := congrArg G.c bad
  norm_num [op, mul, inv, q] at hc
  exact (by decide : (54 : ZMod 5) ≠ 0) hc

end G

def certificate : Goal :=
  ⟨G, G.instMagma, G.source_holds, G.target_fails⟩

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32546_to_43730 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_32546_to_43730
