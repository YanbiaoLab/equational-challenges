-- Equation10776 → Equation55657
-- Recorded verdict: true
-- Premise: x = y * ((z * w) * ((w * y) * x))
-- Conclusion: x * (x * y) = (y * x) * (z * y)
-- Original submission SHA-256: 519eeaa96d4060a4d87917b1a1d285dbc5d4139499f494758498a3d7cfc130b2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((z ◇ w) ◇ ((w ◇ y) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ y) = (y ◇ x) ◇ (z ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), ((q2 ◇ (q3 ◇ q1)) ◇ q0) = (q2 ◇ q0):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => q2 ◇ t) ((h q0 (q3 ◇ q1) q1 q2).symm)).symm).trans ((h ((q2 ◇ (q3 ◇ q1)) ◇ q0) q2 q3 q1).symm)).symm
  have apc1 : forall (q4 q5 q6:G), ((q6 ◇ q4) ◇ q5) = (q6 ◇ q5):=by
    intro q4 q5 q6
    exact ((congrArg (fun t => t ◇ q5) (congrArg (fun t => q6 ◇ t) ((h q4 q4 q4 q4).symm))).symm).trans (apc0 q5 ((q4 ◇ q4) ◇ ((q4 ◇ q4) ◇ q4)) q6 q4)
  have apc2 : forall (q4 q5 q6:G), (q6 ◇ q5) = (q4 ◇ q5):=by
    intro q4 q5 q6
    exact (((congrArg (fun t => t ◇ q5) ((h q4 q6 q4 q4).symm)).symm).trans (apc0 q5 ((q4 ◇ q6) ◇ q4) q6 (q4 ◇ q4))).symm
  have apc3 : forall (q4 q5 q6:G), (q5 ◇ q5) = (q4 ◇ q5):=by
    intro q4 q5 q6
    exact (((apc2 q4 q5 q6).symm).trans (apc2 q5 q5 q6)).symm
  have apc4 : forall (q7 q8 q9:G), (q9 ◇ (q9 ◇ q8)) = (q7 ◇ (q9 ◇ q8)):=by
    intro q7 q8 q9
    exact (((apc3 q7 (q9 ◇ q8) q7).symm).trans (apc1 q8 (q9 ◇ q8) q9)).symm
  have apc6 : forall (q10 q11 q12 q13:G), (q13 ◇ (q13 ◇ q12)) = (q11 ◇ (q10 ◇ q12)):=by
    intro q10 q11 q12 q13
    exact (((congrArg (fun t => q11 ◇ t) (apc2 q10 q12 q13)).symm).trans ((apc4 q11 q12 q13).symm)).symm
  exact (apc6 (x ◇ (x ◇ y)) (x ◇ (x ◇ y)) y x).trans (apc6 z (y ◇ x) y (x ◇ (x ◇ y)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_10776_to_55657 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_10776_to_55657
