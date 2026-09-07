-- Equation20323 → Equation17758
-- Recorded verdict: true
-- Premise: x = (y * z) * ((z * (w * y)) * u)
-- Conclusion: x = (y * z) * (w * (y * (u * w)))
-- Original submission SHA-256: a39a032bf4baa97001cb4e4fad89affaa133f37e57053564b0e57cfd5dd8f7b5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ z) ◇ ((z ◇ (w ◇ y)) ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ z) ◇ (w ◇ (y ◇ (u ◇ w)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc1 : forall (x y z w u:G), y = x:=by
    intro x y z w u
    exact ((h x y z w u).trans ((h y y z w u).symm)).symm
  exact (apc1 x x x x x).trans ((apc1 x ((y ◇ z) ◇ (w ◇ (y ◇ (u ◇ w)))) x x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_20323_to_17758 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_20323_to_17758
