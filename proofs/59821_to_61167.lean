-- Equation59821 → Equation61167
-- Recorded verdict: true
-- Premise: (x * y) * z = w * ((x * w) * y)
-- Conclusion: (x * y) * x = (z * (w * w)) * y
-- Original submission SHA-256: 3f5dcfec944c8c7939c820e9a2b95a6150060bed3fdd4422d044d61f21de84ce
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = w ◇ ((x ◇ w) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ x = (z ◇ (w ◇ w)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), ((q1 ◇ q2) ◇ q3) = ((q1 ◇ q2) ◇ q0):=by
    intro q0 q1 q2 q3
    exact ((h q1 q2 q0 q0).trans ((h q1 q2 q3 q0).symm)).symm
  have apc1 : forall (x y z w:G), ((x ◇ y) ◇ z) = ((x ◇ y) ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x y x w).symm)
  have apc2 : forall (q4 q5 q6 q7 q8 q9:G), ((q7 ◇ q8) ◇ q7) = ((q5 ◇ q6) ◇ q4):=by
    intro q4 q5 q6 q7 q8 q9
    exact ((((apc0 q4 q5 q6 ((q7 ◇ (q5 ◇ q6)) ◇ q8)).symm).trans ((h q7 q8 q9 (q5 ◇ q6)).symm)).trans (apc1 q7 q8 q9 ((q7 ◇ q8) ◇ q9))).symm
  have apc6 : forall (q4 q5 q6 q7 q8 q9:G), ((q7 ◇ q7) ◇ q7) = ((q5 ◇ q6) ◇ q4):=by
    intro q4 q5 q6 q7 q8 q9
    exact (((apc2 q4 q5 q6 q7 q8 q9).symm).trans (apc2 q7 q7 q7 q7 q8 q9)).symm
  exact ((apc6 x x y ((x ◇ y) ◇ x) ((x ◇ y) ◇ x) ((x ◇ y) ◇ x)).symm).trans (apc6 y z (w ◇ w) ((x ◇ y) ◇ x) ((x ◇ y) ◇ x) ((x ◇ y) ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_59821_to_61167 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_59821_to_61167
