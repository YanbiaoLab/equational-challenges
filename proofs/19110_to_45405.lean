-- Equation19110 → Equation45405
-- Recorded verdict: false
-- Premise: x = (y ◇ y) ◇ ((x ◇ z) ◇ (z ◇ y))
-- Conclusion: x ◇ y = y ◇ (((x ◇ y) ◇ y) ◇ y)
-- Original submission SHA-256: 5b8baeba067c23340167aed24f5bb8cccbb68adaf4410c14d495f52188315c97
-- Aurora-accepted correction SHA-256: 872bd708a66a5ec8acb5c904791a54a24832bd44f3b5f63b576f2228763eb424
-- Generator: equational-challenges standalone v2
-- All project definitions are embedded in this file.
import Mathlib.Tactic

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ ((x ◇ z) ◇ (z ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = y ◇ (((x ◇ y) ◇ y) ◇ y)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                     

namespace submission

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Countermodel19110To45405GF2

abbrev V := Fin 5 → ZMod 2

def A (x : V) : V := ![
  x 2 + x 4,
  x 0 + x 3,
  x 1 + x 2,
  x 0 + x 2 + x 3,
  x 1 + x 3 + x 4
]

def B (x : V) : V := ![
  x 3 + x 4,
  x 0 + x 4,
  x 0 + x 1 + x 3 + x 4,
  x 1 + x 2 + x 4,
  x 2 + x 3
]

def op (x y : V) : V := A x + B y

@[reducible] def model : Magma V := ⟨op⟩

local instance : Magma V := model

theorem source : EquationLHS V := by
  change ∀ x y z : V, x = op (op y y) (op (op x z) (op z y))
  intro x y z
  apply funext
  intro coordinate
  fin_cases coordinate <;> simp [op, A, B] <;> ring_nf <;>
    simp only [CharTwo.ofNat_eq_mod] <;> norm_num

def e0 : V := ![1, 0, 0, 0, 0]

theorem target_false : ¬ EquationRHS V := by
  change ¬ ∀ x y : V, op x y = op y (op (op (op x y) y) y)
  intro target
  have bad := congrFun (target (0 : V) e0) 1
  change (1 : ZMod 2) = 0 at bad
  exact one_ne_zero bad

end Countermodel19110To45405GF2

def certificate : Goal :=
  ⟨Countermodel19110To45405GF2.V,
    Countermodel19110To45405GF2.model,
    Countermodel19110To45405GF2.source,
    Countermodel19110To45405GF2.target_false⟩

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19110_to_45405 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_19110_to_45405
