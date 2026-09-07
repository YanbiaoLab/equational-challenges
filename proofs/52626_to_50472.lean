-- Equation52626 → Equation50472
-- Recorded verdict: true
-- Premise: x * y = ((z * (x * w)) * w) * z
-- Conclusion: x * x = (y * ((z * z) * w)) * y
-- Original submission SHA-256: f7b73c62cbffc17702b00d89eccc71d81847904ad69b20175ffc628c5f212668
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ (x ◇ w)) ◇ w) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = (y ◇ ((z ◇ z) ◇ w)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y x x).trans ((h x x x x).symm)
  have apc1 : forall (x y z w:G), (((z ◇ z) ◇ w) ◇ z) = (x ◇ x):=by
    intro x y z w
    exact (((apc0 x x (x ◇ x) (x ◇ x)).symm).trans ((h x x z w).trans (congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ w) (apc0 z (x ◇ w) (z ◇ (x ◇ w)) (z ◇ (x ◇ w))))))).symm
  have apc2 : forall (x y z w:G), (z ◇ z) = (x ◇ x):=by
    intro x y z w
    exact (((apc1 x x z x).symm).trans (apc1 z x z x)).symm
  exact (calc
    (x ◇ x) = ((y ◇ ((z ◇ z) ◇ w)) ◇ (y ◇ ((z ◇ z) ◇ w))):=apc2 (y ◇ ((z ◇ z) ◇ w)) w x w
    _ = ((y ◇ ((z ◇ z) ◇ w)) ◇ y):=(apc0 (y ◇ ((z ◇ z) ◇ w)) y w w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52626_to_50472 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52626_to_50472
