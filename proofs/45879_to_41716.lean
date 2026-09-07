-- Equation45879 → Equation41716
-- Recorded verdict: true
-- Premise: x * y = z * (((w * u) * x) * z)
-- Conclusion: x * x = y * (z * (w * (z * x)))
-- Original submission SHA-256: e27e151ef7d8dc03ca53568ea7b5bfc37561c66422b7bed3fd72809378487e96
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (((w ◇ u) ◇ x) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (z ◇ (w ◇ (z ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y x x x).trans ((h x x x x x).symm)
  have apc1 : forall (x y z w u:G), (z ◇ z) = (x ◇ x):=by
    intro x y z w u
    exact (((apc0 x x (x ◇ x) (x ◇ x) (x ◇ x)).symm).trans ((h x x z x x).trans (apc0 z (((x ◇ x) ◇ x) ◇ z) (z ◇ (((x ◇ x) ◇ x) ◇ z)) (z ◇ (((x ◇ x) ◇ x) ◇ z)) (z ◇ (((x ◇ x) ◇ x) ◇ z))))).symm
  exact (calc
    (x ◇ x) = (y ◇ y):=apc1 y w x w w
    _ = (y ◇ (z ◇ (w ◇ (z ◇ x)))):=(apc0 y (z ◇ (w ◇ (z ◇ x))) w w w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45879_to_41716 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45879_to_41716
