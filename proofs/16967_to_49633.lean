-- Equation16967 → Equation49633
-- Recorded verdict: true
-- Premise: x = y * ((((z * w) * u) * v) * y)
-- Conclusion: x * y = (x * (x * (x * z))) * z
-- Original submission SHA-256: e5c4ee6e2c009bb6fc627d0f892c5860a192e57b6e6771fedfc2ca141f796767
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x = y ◇ ((((z ◇ w) ◇ u) ◇ v) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (x ◇ (x ◇ (x ◇ z))) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w u v:G), y = x:=by
    intro x y z w u v
    exact ((h x y z w u v).trans ((h y y z w u v).symm)).symm
  exact (apc0 (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y)).trans ((apc0 (x ◇ y) ((x ◇ (x ◇ (x ◇ z))) ◇ z) (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_16967_to_49633 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_16967_to_49633
