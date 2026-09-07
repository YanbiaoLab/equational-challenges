-- Equation1821 → Equation49966
-- Recorded verdict: true
-- Premise: x = (y * z) * ((w * w) * x)
-- Conclusion: x * y = (z * (x * (z * y))) * y
-- Original submission SHA-256: 4db80e753f3d784ed7df3bf74750ead5b2696e578159e2d09868609c11f3d771
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ ((w ◇ w) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ (x ◇ (z ◇ y))) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), ((q2 ◇ q3) ◇ q1) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => (q2 ◇ q3) ◇ t) ((h q1 q0 q0 q0).symm)).symm).trans ((h ((q0 ◇ q0) ◇ q1) q2 q3 q0).symm)
  have apc1 : forall (q4 q5 q6 q7:G), ((q6 ◇ q7) ◇ q5) = (q4 ◇ q5):=by
    intro q4 q5 q6 q7
    exact (((congrArg (fun t => t ◇ q5) ((h q4 (q4 ◇ q4) q4 q4).symm)).symm).trans ((apc0 ((q4 ◇ q4) ◇ q4) q5 q6 q7).symm)).symm
  exact ((apc1 x y (x ◇ y) ((z ◇ (x ◇ (z ◇ y))) ◇ y)).symm).trans (apc1 (z ◇ (x ◇ (z ◇ y))) y (x ◇ y) ((z ◇ (x ◇ (z ◇ y))) ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1821_to_49966 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_1821_to_49966
