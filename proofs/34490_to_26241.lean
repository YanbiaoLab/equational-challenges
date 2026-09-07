-- Equation34490 → Equation26241
-- Recorded verdict: true
-- Premise: x = ((y * z) * (w * (u * z))) * z
-- Conclusion: x = (y * ((y * z) * w)) * (w * u)
-- Original submission SHA-256: 032e92d222a69a8a2ae0be142d8892e558a3be9beb90be2b64ca9414ff4b417b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((y ◇ z) ◇ (w ◇ (u ◇ z))) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ ((y ◇ z) ◇ w)) ◇ (w ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z w u:G), y = x:=by
    intro x y z w u
    exact ((h x y z w u).trans ((h y y z w u).symm)).symm
  exact (apc0 x x x x x).trans ((apc0 x ((y ◇ ((y ◇ z) ◇ w)) ◇ (w ◇ u)) x x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_34490_to_26241 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_34490_to_26241
