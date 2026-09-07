-- Equation59681 → Equation62539
-- Recorded verdict: true
-- Premise: (x * y) * z = y * ((y * w) * y)
-- Conclusion: (x * y) * z = ((w * w) * u) * v
-- Original submission SHA-256: afb303bdb7c2d2888e4dd862bd973a7504aa57095be4cbe6e2527ba56e9ee759
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = y ◇ ((y ◇ w) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), (x ◇ y) ◇ z = ((w ◇ w) ◇ u) ◇ v
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have apc0 : forall (x y z w:G), ((y ◇ y) ◇ y) = ((x ◇ y) ◇ z):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y y w).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (((q0 ◇ q0) ◇ q0) ◇ q2) = ((q1 ◇ q1) ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q2) ((apc0 q0 q0 q1 q0).symm)).symm).trans ((apc0 (q0 ◇ q0) q1 q2 q0).symm)
  have apc2 : forall (q3 q4 q5 q6 q7:G), (((q3 ◇ q3) ◇ q3) ◇ q4) = ((q5 ◇ q6) ◇ q7):=by
    intro q3 q4 q5 q6 q7
    exact (apc1 q3 q6 q4).trans (apc0 q5 q6 q7 q3)
  have apc12 : forall (q3 q4 q5 q6 q7:G), ((q5 ◇ q6) ◇ q7) = ((q3 ◇ q3) ◇ q3):=by
    intro q3 q4 q5 q6 q7
    exact ((apc2 q3 q4 q5 q6 q7).symm).trans (apc2 q3 q4 q3 q3 q3)
  exact (apc12 ((x ◇ y) ◇ z) ((x ◇ y) ◇ z) x y z).trans ((apc12 ((x ◇ y) ◇ z) ((x ◇ y) ◇ z) (w ◇ w) u v).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_59681_to_62539 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_59681_to_62539
