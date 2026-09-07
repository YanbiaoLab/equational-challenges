-- Equation45793 → Equation59382
-- Recorded verdict: true
-- Premise: x * y = z * (((w * x) * u) * x)
-- Conclusion: (x * y) * x = z * ((z * x) * z)
-- Original submission SHA-256: 42d81642c96f41a356229b6641b94d80ffb19a7f693418f6b1d2fd4825ddb5a2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (((w ◇ x) ◇ u) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = z ◇ ((z ◇ x) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q4 ◇ ((q0 ◇ q1) ◇ q2)) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => q4 ◇ t) (congrArg (fun t => t ◇ q2) ((h q0 q1 (q0 ◇ q2) q0 q0).symm))).symm).trans ((h q2 q3 q4 q0 (((q0 ◇ q0) ◇ q0) ◇ q0)).symm)
  have apc2 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc4 : forall (q5 q6 q7 q8 q9 q10:G), (((q5 ◇ q5) ◇ q6) ◇ q7) = (q8 ◇ q8):=by
    intro q5 q6 q7 q8 q9 q10
    exact ((((congrArg (fun t => q8 ◇ t) (apc2 q6 q9 (q6 ◇ q9) (q6 ◇ q9) (q6 ◇ q9))).trans (apc2 q8 (q6 ◇ q6) (q8 ◇ (q6 ◇ q6)) (q8 ◇ (q6 ◇ q6)) (q8 ◇ (q6 ◇ q6)))).symm).trans ((((congrArg (fun t => q8 ◇ t) (apc0 q5 q10 q6 q9 (q5 ◇ q5))).symm).trans (apc0 q5 q5 ((q5 ◇ q10) ◇ q6) q7 q8)).trans (congrArg (fun t => t ◇ q7) (congrArg (fun t => t ◇ q6) (apc2 q5 q10 (q5 ◇ q10) (q5 ◇ q10) (q5 ◇ q10)))))).symm
  have apc6 : forall (q11 q12 q13 q14:G), ((q11 ◇ q11) ◇ q12) = (q13 ◇ q13):=by
    intro q11 q12 q13 q14
    exact ((congrArg (fun t => t ◇ q12) (apc2 q11 q14 (q11 ◇ q14) (q11 ◇ q14) (q11 ◇ q14))).symm).trans (((congrArg (fun t => t ◇ q12) ((h q11 q14 (q11 ◇ q11) q11 q11).symm)).symm).trans (apc4 q11 (((q11 ◇ q11) ◇ q11) ◇ q11) q12 q13 q11 q11))
  have apc7 : forall (q11 q14 q12 q13:G), ((q13 ◇ q13) ◇ q13) = ((q11 ◇ q11) ◇ q12):=by
    intro q11 q14 q12 q13
    exact ((apc6 q11 q12 q13 q14).trans ((apc6 q13 q13 q13 q14).symm)).symm
  have apc9 : forall (q15 q16:G), ((q15 ◇ q15) ◇ (q15 ◇ q15)) = ((q16 ◇ q16) ◇ q16):=by
    intro q15 q16
    exact ((apc7 q15 q15 q15 q16).trans (apc2 (q15 ◇ q15) q15 q15 q15 q15)).symm
  have apc10 : forall (q17 q18 q19:G), (((q17 ◇ q17) ◇ q17) ◇ ((q17 ◇ q17) ◇ q17)) = ((q18 ◇ q18) ◇ q18):=by
    intro q17 q18 q19
    exact ((apc2 ((q17 ◇ q17) ◇ q17) ((q19 ◇ q19) ◇ (q19 ◇ q19)) (((q17 ◇ q17) ◇ q17) ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) (((q17 ◇ q17) ◇ q17) ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) (((q17 ◇ q17) ◇ q17) ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19)))).symm).trans (((congrArg (fun t => t ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) (apc9 q19 q17)).symm).trans (apc9 (q19 ◇ q19) q18))
  have apc11 : forall (q20 q21 q22 q23 q24:G), (((q21 ◇ q21) ◇ q21) ◇ ((q20 ◇ q20) ◇ q21)) = ((q22 ◇ q22) ◇ q22):=by
    intro q20 q21 q22 q23 q24
    exact (((congrArg (fun t => ((q21 ◇ q21) ◇ q21) ◇ t) (congrArg (fun t => t ◇ q21) (congrArg (fun t => q20 ◇ t) (congrArg (fun t => t ◇ q21) (congrArg (fun t => t ◇ q23) (apc2 q24 q21 (q24 ◇ q21) (q24 ◇ q21) (q24 ◇ q21))))))).trans (congrArg (fun t => ((q21 ◇ q21) ◇ q21) ◇ t) (congrArg (fun t => t ◇ q21) (apc2 q20 (((q24 ◇ q24) ◇ q23) ◇ q21) (q20 ◇ (((q24 ◇ q24) ◇ q23) ◇ q21)) (q20 ◇ (((q24 ◇ q24) ◇ q23) ◇ q21)) (q20 ◇ (((q24 ◇ q24) ◇ q23) ◇ q21)))))).symm).trans (((congrArg (fun t => ((q21 ◇ q21) ◇ q21) ◇ t) (congrArg (fun t => t ◇ q21) (h q21 q21 q20 q24 q23))).symm).trans (apc10 q21 q22 q23))
  have apc12 : forall (q25 q26 q27:G), ((q27 ◇ q27) ◇ q27) = (q26 ◇ q25):=by
    intro q25 q26 q27
    exact ((h q26 q25 ((q26 ◇ q26) ◇ q26) q25 (q25 ◇ q26)).trans (apc11 (q25 ◇ q26) q26 q27 q25 q25)).symm
  exact ((apc12 x (x ◇ y) ((x ◇ y) ◇ x)).symm).trans (apc12 ((z ◇ x) ◇ z) z ((x ◇ y) ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45793_to_59382 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45793_to_59382
