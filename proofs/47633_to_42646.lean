-- Equation47633 → Equation42646
-- Recorded verdict: true
-- Premise: x * y = (z * w) * ((u * x) * z)
-- Conclusion: x * y = x * (y * ((x * x) * x))
-- Original submission SHA-256: 34765f01a1021c6700ccc7be29e4b6951870c63f01970928bb67cb8a8ac66435
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ w) ◇ ((u ◇ x) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = x ◇ (y ◇ ((x ◇ x) ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  exact (apc0 x y (x ◇ y) (x ◇ y) (x ◇ y)).trans ((apc0 x (y ◇ ((x ◇ x) ◇ x)) (x ◇ y) (x ◇ y) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47633_to_42646 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47633_to_42646
