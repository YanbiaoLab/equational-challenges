-- Equation8652 → Equation49565
-- Recorded verdict: false
-- Premise: x = y ◇ (y ◇ (((z ◇ y) ◇ y) ◇ x))
-- Conclusion: x ◇ x = (y ◇ (z ◇ (y ◇ x))) ◇ x
-- Original submission SHA-256: 536888a74013c63e182f00b5255b3a7609be5381187f7a91681325f76e215d3e
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ (((z ◇ y) ◇ y) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (y ◇ (z ◇ (y ◇ x))) ◇ x
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
-- stage:stage0_scalar_affine_prime_power_stream_v2
                   
                     

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace MemoFinOp

abbrev d6Carrier := Fin 27

def d6Affine (i j : Fin 27) : Fin 27 :=
  (6 : Fin 27) * i + (1 : Fin 27) * j + (0 : Fin 27)

@[reducible] def d6Magma : Magma (Fin 27) := { op := d6Affine }

local instance : Magma (Fin 27) := d6Magma

def d6Source : EquationLHS (Fin 27) := by
  intro x y z
  change x = d6Affine (y) (d6Affine (y) (d6Affine (d6Affine (d6Affine (z) (y)) (y)) (x)))
  apply Fin.ext
  simp [d6Affine] <;> omega

def d6Target : ¬ EquationRHS (Fin 27) := by
  intro h
  have bad := h (0 : Fin 27) (1 : Fin 27) (0 : Fin 27)
  change d6Affine ((0 : Fin 27)) ((0 : Fin 27)) = d6Affine (d6Affine ((1 : Fin 27)) (d6Affine ((0 : Fin 27)) (d6Affine ((1 : Fin 27)) ((0 : Fin 27))))) ((0 : Fin 27)) at bad
  change (0 : Fin 27) = (18 : Fin 27) at bad
  exact (show (0 : Fin 27) ≠ (18 : Fin 27) by decide) bad

end MemoFinOp

def submission : Goal := by
  exact ⟨MemoFinOp.d6Carrier, MemoFinOp.d6Magma, MemoFinOp.d6Source, MemoFinOp.d6Target⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_8652_to_49565 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_8652_to_49565
