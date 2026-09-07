-- Equation20214 → Equation17590
-- Recorded verdict: true
-- Premise: x = (y * z) * ((y * (y * z)) * w)
-- Conclusion: x = (y * z) * (y * (z * (x * y)))
-- Original submission SHA-256: a47aa7f1a604e77e2199a9ddb52f2d1fe633d9a847d74463be1b080d5d64b4d2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ ((y ◇ (y ◇ z)) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ (y ◇ (z ◇ (x ◇ y)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc1 : forall (x y z w:G), y = x:=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  exact (apc1 x x x x).trans ((apc1 x ((y ◇ z) ◇ (y ◇ (z ◇ (x ◇ y)))) x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_20214_to_17590 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_20214_to_17590
