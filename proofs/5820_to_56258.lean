-- Equation5820 → Equation56258
-- Recorded verdict: false
-- Premise: x = y ◇ (x ◇ (y ◇ ((x ◇ z) ◇ z)))
-- Conclusion: x ◇ (y ◇ z) = (z ◇ z) ◇ (y ◇ x)
-- Original submission SHA-256: e7de1c4e8c267fb53ad8203040c17b4e8333dc6829f1b7b65995d82a762d23f8
-- Aurora-accepted correction SHA-256: d5a21d31cee85331ad6eee819431fb6ea827aa01b8b9aca9534119be1b157335
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (y ◇ ((x ◇ z) ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = (z ◇ z) ◇ (y ◇ x)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
-- stage:stage0_d15_exp5_group_core
                   
                              
                             
                                 

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

def op (x y : G) : G := coreOp y x

instance instMagma : Magma G where
  op := op

lemma source_holds : EquationLHS G := by
  intro x y z
  change x = op y (op x (op y (op (op x z) z)))
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
  have bad := target (⟨0, 0, 0, 0⟩ : G) (⟨1, 0, 0, 0⟩ : G) (⟨0, 0, 0, 1⟩ : G)
  have hc := congrArg G.c bad
  change ((G.op (⟨0, 0, 0, 0⟩ : G) (G.op (⟨1, 0, 0, 0⟩ : G) (⟨0, 0, 0, 1⟩ : G)))).c = ((G.op (G.op (⟨0, 0, 0, 1⟩ : G) (⟨0, 0, 0, 1⟩ : G)) (G.op (⟨1, 0, 0, 0⟩ : G) (⟨0, 0, 0, 0⟩ : G)))).c at hc
  exact (show Not (((G.op (⟨0, 0, 0, 0⟩ : G) (G.op (⟨1, 0, 0, 0⟩ : G) (⟨0, 0, 0, 1⟩ : G)))).c = ((G.op (G.op (⟨0, 0, 0, 1⟩ : G) (⟨0, 0, 0, 1⟩ : G)) (G.op (⟨1, 0, 0, 0⟩ : G) (⟨0, 0, 0, 0⟩ : G)))).c) from by decide) hc

end G

def certificate : Goal :=
  ⟨G, G.instMagma, G.source_holds, G.target_fails⟩

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5820_to_56258 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_5820_to_56258
