-- Equation45263 → Equation60827
-- Recorded verdict: true
-- Premise: x * y = x * (((x * z) * x) * w)
-- Conclusion: (x * x) * x = (x * (x * y)) * z
-- Original submission SHA-256: b03d827c4e1e126e59ef1dd9ffe80c58b743324a44c3d4db1ee4c20319af214b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = x ◇ (((x ◇ z) ◇ x) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ x = (x ◇ (x ◇ y)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  exact (calc
    ((x ◇ x) ◇ x) = ((x ◇ (x ◇ y)) ◇ x):=congrArg (fun t => t ◇ x) ((apc0 x (x ◇ y) x x).symm)
    _ = ((x ◇ (x ◇ y)) ◇ (x ◇ (x ◇ y))):=apc0 (x ◇ (x ◇ y)) x x x
    _ = ((x ◇ (x ◇ y)) ◇ z):=(apc0 (x ◇ (x ◇ y)) z x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45263_to_60827 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45263_to_60827
