-- Equation52578 → Equation61992
-- Recorded verdict: true
-- Premise: x * y = ((z * (x * y)) * x) * w
-- Conclusion: (x * y) * x = ((z * x) * w) * w
-- Original submission SHA-256: 73044f21627248ec75d00b483562d60ed88a89f092c17736ac7503bdc240e615
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ (x ◇ y)) ◇ x) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ x = ((z ◇ x) ◇ w) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (((q2 ◇ q3) ◇ q0) ◇ q1) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q1) ((h (q2 ◇ q3) q0 q0 q2).symm)).symm).trans ((h q2 q3 (q0 ◇ ((q2 ◇ q3) ◇ q0)) q1).symm)
  have apc1 : forall (q4 q5 q6 q7:G), ((q4 ◇ q5) ◇ q7) = ((q4 ◇ q5) ◇ q6):=by
    intro q4 q5 q6 q7
    exact (((congrArg (fun t => t ◇ q6) (apc0 q7 q4 q4 q5)).symm).trans (apc0 q4 q6 (q4 ◇ q5) q7)).symm
  have apc2 : forall (q4 q5 q6 q7:G), ((q4 ◇ q5) ◇ q6) = ((q4 ◇ q5) ◇ q4):=by
    intro q4 q5 q6 q7
    exact ((apc1 q4 q5 q6 q7).symm).trans (apc1 q4 q5 q4 q7)
  have apc3 : forall (q8 q9 q10 q11 q12:G), ((q8 ◇ q9) ◇ q8) = (q10 ◇ q11):=by
    intro q8 q9 q10 q11 q12
    exact ((apc2 q8 q9 q12 ((q8 ◇ q9) ◇ q12)).symm).trans (((congrArg (fun t => t ◇ q12) (apc0 (q10 ◇ q11) q10 q8 q9)).symm).trans ((h q10 q11 (q8 ◇ q9) q12).symm))
  have apc4 : forall (q8 q9 q12 q10 q11:G), ((q10 ◇ q10) ◇ q10) = ((q8 ◇ q9) ◇ q8):=by
    intro q8 q9 q12 q10 q11
    exact ((apc3 q8 q9 q10 q11 q12).trans ((apc3 q10 q10 q10 q11 q12).symm)).symm
  have apc9 : forall (q13 q14 q15:G), ((q15 ◇ q15) ◇ q15) = (q13 ◇ q14):=by
    intro q13 q14 q15
    exact (((apc0 q13 (q13 ◇ q14) q13 q14).symm).trans (((congrArg (fun t => t ◇ (q13 ◇ q14)) (apc2 q13 q14 q13 q13)).symm).trans ((apc4 (q13 ◇ q14) q13 q13 q15 q13).symm))).symm
  exact ((apc9 (x ◇ y) x ((x ◇ y) ◇ x)).symm).trans (apc9 ((z ◇ x) ◇ w) w ((x ◇ y) ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52578_to_61992 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52578_to_61992
