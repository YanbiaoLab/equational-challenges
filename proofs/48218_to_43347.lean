-- Equation48218 → Equation43347
-- Recorded verdict: true
-- Premise: x * y = (z * (x * z)) * (z * w)
-- Conclusion: x * x = y * ((x * y) * (x * z))
-- Original submission SHA-256: a3cc906c055f8a61bb9881f3798aee8f0fd343ee20410fc18264b13d0b823ca6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (x ◇ z)) ◇ (z ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ ((x ◇ y) ◇ (x ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y x x).trans ((h x x x x).symm)
  have apc1 : forall (x y z w:G), ((z ◇ z) ◇ (z ◇ w)) = (x ◇ x):=by
    intro x y z w
    exact (((apc0 x x (x ◇ x) (x ◇ x)).symm).trans ((h x x z w).trans ((congrArg (fun t => t ◇ (z ◇ w)) (congrArg (fun t => z ◇ t) (apc0 x z (x ◇ z) (x ◇ z)))).trans (congrArg (fun t => t ◇ (z ◇ w)) (apc0 z (x ◇ x) (z ◇ (x ◇ x)) (z ◇ (x ◇ x))))))).symm
  have apc2 : forall (x y z w:G), (z ◇ z) = (x ◇ x):=by
    intro x y z w
    exact (((apc1 x x z x).symm).trans (apc1 z x z x)).symm
  have apc4 : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ (q2 ◇ q0)) = (q2 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q2 ◇ q0)) (apc0 q2 ((q0 ◇ q0) ◇ (q0 ◇ q0)) (q2 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (q2 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))).symm).trans (((congrArg (fun t => t ◇ (q2 ◇ q0)) (congrArg (fun t => q2 ◇ t) ((apc1 q2 q0 q0 q0).symm))).symm).trans ((h q2 q1 q2 q0).symm))
  have apc6 : forall (q3 q4 q5:G), (q5 ◇ q5) = (q4 ◇ q3):=by
    intro q3 q4 q5
    exact (((apc4 q4 q3 q4).symm).trans (apc2 q5 q3 (q4 ◇ q4) q3)).symm
  exact (apc6 (x ◇ x) (x ◇ x) x).trans (apc6 ((x ◇ y) ◇ (x ◇ z)) y (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48218_to_43347 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48218_to_43347
