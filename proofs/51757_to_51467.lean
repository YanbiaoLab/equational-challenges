-- Equation51757 → Equation51467
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * (w * u)) * v
-- Conclusion: x * y = ((x * z) * (x * w)) * z
-- Original submission SHA-256: 9fe52696844787e7c5dae9698893b5f6cd17e44a1a41c1928b7f8eae8da71434
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = ((z ◇ x) ◇ (w ◇ u)) ◇ v
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((x ◇ z) ◇ (x ◇ w)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc1 : forall (x y z w u v:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u v
    exact (h x y z w u v).trans ((h x x z w u v).symm)
  have apc3 : forall (q0 q1 q2 q3:G), (((q2 ◇ q1) ◇ (q2 ◇ q1)) ◇ q0) = (q1 ◇ q1):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => t ◇ q0) (apc1 (q2 ◇ q1) (q0 ◇ q0) q0 q0 q0 q0)).symm).trans ((h q1 q3 q2 q0 q0 q0).symm)).trans (apc1 q1 q3 (q1 ◇ q3) (q1 ◇ q3) (q1 ◇ q3) (q1 ◇ q3))
  have apc5 : forall (x y z w u v:G), (((z ◇ x) ◇ (w ◇ u)) ◇ v) = (x ◇ x):=by
    intro x y z w u v
    exact (((h x y z w u v).symm).trans (h x y x x x x)).trans (apc3 x x x (((x ◇ x) ◇ (x ◇ x)) ◇ x))
  exact (calc
    (x ◇ y) = (x ◇ x):=apc1 x y (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y)
    _ = (((x ◇ z) ◇ (x ◇ w)) ◇ z):=((congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ (x ◇ w)) (apc1 x z (x ◇ z) (x ◇ z) (x ◇ z) (x ◇ z)))).trans (apc5 x (((x ◇ x) ◇ (x ◇ w)) ◇ z) x x w z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51757_to_51467 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51757_to_51467
