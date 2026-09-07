-- Equation3061 → Equation3071
-- Recorded verdict: true
-- Premise: x = (((x ◇ x) ◇ y) ◇ z) ◇ x
-- Conclusion: x = (((x ◇ y) ◇ x) ◇ z) ◇ x
-- Original submission SHA-256: 8e9483e0fc7657c496a81744f4331713027537591b093049c3cf2fb7392466bc
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((x ◇ x) ◇ y) ◇ z) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((x ◇ y) ◇ x) ◇ z) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc5 : forall (q0 q1 q2:G), ((q1 ◇ q2) ◇ ((q1 ◇ q1) ◇ q0)) = ((q1 ◇ q1) ◇ q0):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ ((q1 ◇ q1) ◇ q0)) (congrArg (fun t => t ◇ q2) ((h q1 q0 ((q1 ◇ q1) ◇ q0)).symm))).symm).trans ((h ((q1 ◇ q1) ◇ q0) q1 q2).symm)
  have apc6 : forall (q3 q4 q5 q6:G), (((q4 ◇ q4) ◇ q3) ◇ (((q4 ◇ q5) ◇ (q4 ◇ q5)) ◇ q6)) = (((q4 ◇ q5) ◇ (q4 ◇ q5)) ◇ q6):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => t ◇ (((q4 ◇ q5) ◇ (q4 ◇ q5)) ◇ q6)) (apc5 q3 q4 q5)).symm).trans (apc5 q6 (q4 ◇ q5) ((q4 ◇ q4) ◇ q3))
  have apc7 : forall (q7 q8 q9:G), ((((q9 ◇ q7) ◇ (q9 ◇ q7)) ◇ q8) ◇ q9) = q9:=by
    intro q7 q8 q9
    exact ((congrArg (fun t => t ◇ q9) (apc6 q7 q9 q7 q8)).symm).trans ((h q9 q7 (((q9 ◇ q7) ◇ (q9 ◇ q7)) ◇ q8)).symm)
  have apc9 : forall (q10 q7 q8 q11:G), (((((q10 ◇ q7) ◇ (q10 ◇ q7)) ◇ q8) ◇ q11) ◇ (q10 ◇ q10)) = (q10 ◇ q10):=by
    intro q10 q7 q8 q11
    exact ((congrArg (fun t => t ◇ (q10 ◇ q10)) (congrArg (fun t => t ◇ q11) (apc6 (q10 ◇ q10) q10 q7 q8))).symm).trans ((h (q10 ◇ q10) (((q10 ◇ q7) ◇ (q10 ◇ q7)) ◇ q8) q11).symm)
  have apc10 : forall (q12 q13 q14 q15:G), (((((q13 ◇ q13) ◇ q12) ◇ ((q13 ◇ q13) ◇ q12)) ◇ q15) ◇ (q13 ◇ q14)) = (q13 ◇ q14):=by
    intro q12 q13 q14 q15
    exact ((congrArg (fun t => t ◇ (q13 ◇ q14)) (congrArg (fun t => t ◇ q15) (congrArg (fun t => ((q13 ◇ q13) ◇ q12) ◇ t) (apc5 q12 q13 q14)))).symm).trans (((congrArg (fun t => t ◇ (q13 ◇ q14)) (congrArg (fun t => t ◇ q15) (congrArg (fun t => t ◇ ((q13 ◇ q14) ◇ ((q13 ◇ q13) ◇ q12))) (apc5 q12 q13 q14)))).symm).trans (apc7 ((q13 ◇ q13) ◇ q12) q15 (q13 ◇ q14)))
  have apc11 : forall (q16 q17 q18:G), ((q16 ◇ q16) ◇ ((q16 ◇ q17) ◇ q18)) = ((q16 ◇ q17) ◇ q18):=by
    intro q16 q17 q18
    exact ((congrArg (fun t => t ◇ ((q16 ◇ q17) ◇ q18)) (apc9 q16 q17 q16 (((q16 ◇ q17) ◇ (q16 ◇ q17)) ◇ q16))).symm).trans (apc10 q16 (q16 ◇ q17) q18 (q16 ◇ q16))
  have apc12 : forall (q19 q20 q21 q22:G), ((((q21 ◇ q19) ◇ q20) ◇ q22) ◇ q21) = q21:=by
    intro q19 q20 q21 q22
    exact ((congrArg (fun t => t ◇ q21) (congrArg (fun t => t ◇ q22) (apc11 q21 q19 q20))).symm).trans ((h q21 ((q21 ◇ q19) ◇ q20) q22).symm)
  exact (calc
    x = x:=rfl
    _ = ((((x ◇ y) ◇ x) ◇ z) ◇ x):=(apc12 y x x z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3061_to_3071 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3061_to_3071
