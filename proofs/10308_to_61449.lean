-- Equation10308 → Equation61449
-- Recorded verdict: true
-- Premise: x = y * ((x * z) * ((w * u) * w))
-- Conclusion: (x * y) * z = (y * (z * z)) * z
-- Original submission SHA-256: c2041e85e77ed011a30b3d1b6f735680eb9d910eea4910ea138a9eddc477d593
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ ((x ◇ z) ◇ ((w ◇ u) ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = (y ◇ (z ◇ z)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (q3 ◇ ((q1 ◇ q0) ◇ q1)) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q3 ◇ t) ((h ((q1 ◇ q0) ◇ q1) (q2 ◇ q0) q0 q1 q0).symm)).symm).trans ((h q2 q3 q0 ((q1 ◇ q0) ◇ q1) q0).symm)
  have apc1 : forall (q4 q5 q6:G), ((q6 ◇ q5) ◇ q6) = q4:=by
    intro q4 q5 q6
    exact (((apc0 q4 ((q6 ◇ q5) ◇ q6) q4 q4).symm).trans ((h ((q6 ◇ q5) ◇ q6) q4 q4 q6 q5).symm)).symm
  exact ((apc1 ((x ◇ y) ◇ z) ((y ◇ (z ◇ z)) ◇ z) ((x ◇ y) ◇ z)).symm).trans (apc1 ((y ◇ (z ◇ z)) ◇ z) ((y ◇ (z ◇ z)) ◇ z) ((x ◇ y) ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_10308_to_61449 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_10308_to_61449
