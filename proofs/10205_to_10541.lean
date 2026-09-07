-- Equation10205 → Equation10541
-- Recorded verdict: false
-- Premise: x = y ◇ ((x ◇ y) ◇ ((x ◇ z) ◇ z))
-- Conclusion: x = y ◇ ((z ◇ y) ◇ ((x ◇ x) ◇ z))
-- Original submission SHA-256: 4f25b643aa400172b222ead255260ed584deb0f8e96058f461a5307d4505d347
-- Aurora-accepted correction SHA-256: 598fd9004e75502615d9b3d022e50f74f61f1cbd8a67173a1569b4e2343f001c
-- Generator: equational-challenges standalone v2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ y) ◇ ((x ◇ z) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ y) ◇ ((x ◇ x) ◇ z))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                              
                             
                                 

open scoped Fin.CommRing

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace submission

@[ext] structure G where
  a : Fin 5
  b : Fin 5
  c : Fin 5
  d : Fin 5

namespace G

def q (x : Fin 5) : Fin 5 := 3 * x * (x + 1)

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

def coreOp (x y : G) : G := mul (mul x (inv y)) x

-- Opposite of the Judge-accepted Equation32546→Equation43730 model.
def op (x y : G) : G := coreOp y x

instance instMagma : Magma G where
  op := op

lemma source_holds : EquationLHS G := by
  intro x y z
  change x = op y (op (op x y) (op (op x z) z))
  rcases x with ⟨xa, xb, xc, xd⟩
  rcases y with ⟨ya, yb, yc, yd⟩
  rcases z with ⟨za, zb, zc, zd⟩
  have h6 : (6 : Fin 5) = 1 := by decide
  have h5 : (5 : Fin 5) = 0 := by decide
  have h15 : (15 : Fin 5) = 0 := by decide
  have h20 : (20 : Fin 5) = 0 := by decide
  have h25 : (25 : Fin 5) = 0 := by decide
  have h40 : (40 : Fin 5) = 0 := by decide
  have h45 : (45 : Fin 5) = 0 := by decide
  have h55 : (55 : Fin 5) = 0 := by decide
  have h70 : (70 : Fin 5) = 0 := by decide
  have h80 : (80 : Fin 5) = 0 := by decide
  have h100 : (100 : Fin 5) = 0 := by decide
  have h105 : (105 : Fin 5) = 0 := by decide
  have h120 : (120 : Fin 5) = 0 := by decide
  have h130 : (130 : Fin 5) = 0 := by decide
  have h145 : (145 : Fin 5) = 0 := by decide
  have h165 : (165 : Fin 5) = 0 := by decide
  have h200 : (200 : Fin 5) = 0 := by decide
  have h240 : (240 : Fin 5) = 0 := by decide
  apply G.ext <;> simp [op, coreOp, mul, inv, q] <;> ring_nf
  all_goals simp only [h6, h5, h15, h20, h25, h40, h45, h55, h70, h80, h100, h105, h120, h130, h145, h165, h200, h240, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero]

lemma target_fails : ¬ EquationRHS G := by
  intro target
  have bad := target
    (⟨0, 0, 0, 0⟩ : G)
    (⟨1, 0, 0, 0⟩ : G)
    (⟨0, 0, 0, 1⟩ : G)
  have hc := congrArg G.c bad
  change (0 : Fin 5) =
    (op (⟨1, 0, 0, 0⟩ : G)
      (op (op (⟨0, 0, 0, 1⟩ : G) (⟨1, 0, 0, 0⟩ : G))
        (op (op (⟨0, 0, 0, 0⟩ : G) (⟨0, 0, 0, 0⟩ : G))
          (⟨0, 0, 0, 1⟩ : G)))).c at hc
  have h6t : (6 : Fin 5) = 1 := by decide
  have h5t : (5 : Fin 5) = 0 := by decide
  have h15t : (15 : Fin 5) = 0 := by decide
  have h20t : (20 : Fin 5) = 0 := by decide
  have h25t : (25 : Fin 5) = 0 := by decide
  have h40t : (40 : Fin 5) = 0 := by decide
  have h45t : (45 : Fin 5) = 0 := by decide
  have h55t : (55 : Fin 5) = 0 := by decide
  have h70t : (70 : Fin 5) = 0 := by decide
  have h80t : (80 : Fin 5) = 0 := by decide
  have h100t : (100 : Fin 5) = 0 := by decide
  have h105t : (105 : Fin 5) = 0 := by decide
  have h120t : (120 : Fin 5) = 0 := by decide
  have h130t : (130 : Fin 5) = 0 := by decide
  have h145t : (145 : Fin 5) = 0 := by decide
  have h165t : (165 : Fin 5) = 0 := by decide
  have h200t : (200 : Fin 5) = 0 := by decide
  have h240t : (240 : Fin 5) = 0 := by decide
  simp [op, coreOp, mul, inv, q] at hc
  ring_nf at hc
  exact (by decide : Not ((0 : Fin 5) = (-373 : Fin 5))) hc

end G

def certificate : Goal :=
  ⟨G, G.instMagma, G.source_holds, G.target_fails⟩

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_10205_to_10541 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_10205_to_10541
