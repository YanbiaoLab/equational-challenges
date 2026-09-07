-- Equation46513 → Equation56984
-- Recorded verdict: true
-- Premise: x * y = (z * y) * (y * (x * x))
-- Conclusion: x * (y * z) = (x * (z * y)) * w
-- Original submission SHA-256: 36172109bc7e4c4d526f2724ea6d80ba0125e4383fc6ef346ba438dd629ece42
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ y) ◇ (y ◇ (x ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (x ◇ (z ◇ y)) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z:G), ((z ◇ y) ◇ (y ◇ (x ◇ x))) = ((x ◇ y) ◇ (y ◇ (x ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q1 ◇ (q0 ◇ q0))) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((apc0 q0 q1 q0).symm).trans ((h q0 q1 q0).symm)
  have apc3 : forall (q2 q3 q4:G), ((q4 ◇ (q3 ◇ (q2 ◇ q2))) ◇ (q2 ◇ (q2 ◇ q2))) = ((q2 ◇ q2) ◇ (q3 ◇ (q2 ◇ q2))):=by
    intro q2 q3 q4
    exact ((congrArg (fun t => (q4 ◇ (q3 ◇ (q2 ◇ q2))) ◇ t) ((h q2 (q2 ◇ q2) q3).symm)).symm).trans ((h (q2 ◇ q2) (q3 ◇ (q2 ◇ q2)) q4).symm)
  have apc4 : forall (q2 q5 q6:G), ((q2 ◇ q5) ◇ ((q5 ◇ (q2 ◇ q2)) ◇ (q6 ◇ q6))) = (q6 ◇ (q5 ◇ (q2 ◇ q2))):=by
    intro q2 q5 q6
    exact ((congrArg (fun t => t ◇ ((q5 ◇ (q2 ◇ q2)) ◇ (q6 ◇ q6))) ((h q2 q5 q2).symm)).symm).trans ((h q6 (q5 ◇ (q2 ◇ q2)) (q2 ◇ q5)).symm)
  have apc5 : forall (q7 q8:G), ((q8 ◇ q8) ◇ (q7 ◇ (q8 ◇ q8))) = (q8 ◇ q8):=by
    intro q7 q8
    exact ((apc3 q8 q7 (q8 ◇ q8)).symm).trans ((((congrArg (fun t => t ◇ (q8 ◇ (q8 ◇ q8))) (apc3 q8 q7 q7)).symm).trans (apc3 q8 q8 (q7 ◇ (q7 ◇ (q8 ◇ q8))))).trans (apc1 q8 q8))
  have apc7 : forall (q9 q10:G), ((q10 ◇ (q9 ◇ q9)) ◇ (q9 ◇ q9)) = ((q9 ◇ q9) ◇ (q9 ◇ q9)):=by
    intro q9 q10
    exact ((congrArg (fun t => (q10 ◇ (q9 ◇ q9)) ◇ t) (apc5 (q9 ◇ q9) q9)).symm).trans ((h (q9 ◇ q9) (q9 ◇ q9) q10).symm)
  have apc8 : forall (q11:G), (((q11 ◇ q11) ◇ (q11 ◇ q11)) ◇ ((q11 ◇ q11) ◇ (q11 ◇ q11))) = (q11 ◇ q11):=by
    intro q11
    exact (((apc5 (q11 ◇ q11) q11).symm).trans (((congrArg (fun t => t ◇ ((q11 ◇ q11) ◇ (q11 ◇ q11))) (apc5 (q11 ◇ q11) q11)).symm).trans (apc7 (q11 ◇ q11) (q11 ◇ q11)))).symm
  have apc10 : forall (q12:G), (q12 ◇ (q12 ◇ q12)) = (q12 ◇ q12):=by
    intro q12
    exact (((apc8 q12).symm).trans ((h q12 (q12 ◇ q12) (q12 ◇ q12)).symm)).symm
  have apc11 : forall (q13 q14:G), ((q14 ◇ q13) ◇ (q13 ◇ q13)) = (q13 ◇ q13):=by
    intro q13 q14
    exact ((congrArg (fun t => (q14 ◇ q13) ◇ t) (apc10 q13)).symm).trans ((h q13 q13 q14).symm)
  have apc13 : forall (q15 q16:G), ((q15 ◇ q16) ◇ (q15 ◇ q15)) = (q15 ◇ q15):=by
    intro q15 q16
    exact ((congrArg (fun t => (q15 ◇ q16) ◇ t) (apc11 q15 q15)).symm).trans ((((congrArg (fun t => (q15 ◇ q16) ◇ t) (apc11 (q15 ◇ q15) q16)).symm).trans (apc4 q15 q16 (q15 ◇ q15))).trans (apc5 q16 q15))
  have apc14 : forall (q17 q18:G), (q18 ◇ (q18 ◇ q17)) = (q18 ◇ q18):=by
    intro q17 q18
    exact (((apc13 q18 (q18 ◇ q17)).symm).trans (((congrArg (fun t => (q18 ◇ (q18 ◇ q17)) ◇ t) (apc13 q18 q17)).symm).trans (apc1 q18 (q18 ◇ q17)))).symm
  have apc15 : forall (q19 q20:G), ((q20 ◇ q19) ◇ (q20 ◇ q19)) = (q19 ◇ q19):=by
    intro q19 q20
    exact (((apc11 q19 q20).symm).trans (((congrArg (fun t => (q20 ◇ q19) ◇ t) (apc11 q19 q20)).symm).trans (apc14 (q19 ◇ q19) (q20 ◇ q19)))).symm
  have apc16 : forall (q21 q22:G), (q22 ◇ q22) = (q21 ◇ q21):=by
    intro q21 q22
    exact (((congrArg (fun t => (q22 ◇ q22) ◇ t) (apc14 q21 q22)).trans (apc11 q22 q22)).symm).trans ((((congrArg (fun t => t ◇ (q22 ◇ (q22 ◇ q21))) (apc14 q21 q22)).symm).trans (apc15 (q22 ◇ q21) q22)).trans (apc15 q21 q22))
  have apc18 : forall (q23 q24 q25:G), (q24 ◇ (q23 ◇ q23)) = (q23 ◇ q23):=by
    intro q23 q24 q25
    exact (((((congrArg (fun t => (q23 ◇ q23) ◇ t) (congrArg (fun t => t ◇ (q24 ◇ q24)) (apc13 q23 q25))).trans (apc14 (q24 ◇ q24) (q23 ◇ q23))).trans (apc11 q23 q23)).symm).trans ((((congrArg (fun t => t ◇ (((q23 ◇ q25) ◇ (q23 ◇ q23)) ◇ (q24 ◇ q24))) (apc14 q25 q23)).symm).trans (apc4 q23 (q23 ◇ q25) q24)).trans (congrArg (fun t => q24 ◇ t) (apc13 q23 q25)))).symm
  have apc19 : forall (q0 q1:G), (q0 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((((congrArg (fun t => (q0 ◇ q1) ◇ t) (apc18 q0 q1 (q1 ◇ (q0 ◇ q0)))).trans (apc18 q0 (q0 ◇ q1) ((q0 ◇ q1) ◇ (q0 ◇ q0)))).symm).trans (apc1 q0 q1)).symm
  exact (calc
    (x ◇ (y ◇ z)) = (x ◇ x):=apc19 x (y ◇ z)
    _ = ((x ◇ (z ◇ y)) ◇ (x ◇ (z ◇ y))):=apc16 (x ◇ (z ◇ y)) x
    _ = ((x ◇ (z ◇ y)) ◇ w):=(apc19 (x ◇ (z ◇ y)) w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46513_to_56984 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46513_to_56984
