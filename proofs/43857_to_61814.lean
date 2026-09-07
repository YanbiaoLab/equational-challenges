-- Equation43857 → Equation61814
-- Recorded verdict: true
-- Premise: x * y = z * ((x * w) * (w * w))
-- Conclusion: (x * x) * y = ((y * z) * y) * y
-- Original submission SHA-256: 8b65534885fce2a192c96e6788c47ebe94970a20a990f9583b154b7ab882aac3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((x ◇ w) ◇ (w ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ y = ((y ◇ z) ◇ y) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((apc0 q1 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q0 q0).symm).trans ((h q0 q2 q1 q0).symm)).trans (apc0 q0 q2 (q0 ◇ q2) (q0 ◇ q2))
  exact (calc
    ((x ◇ x) ◇ y) = (((y ◇ z) ◇ (y ◇ z)) ◇ y):=congrArg (fun t => t ◇ y) (apc1 (y ◇ z) x x)
    _ = (((y ◇ z) ◇ y) ◇ y):=(congrArg (fun t => t ◇ y) (apc0 (y ◇ z) y x x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43857_to_61814 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43857_to_61814
