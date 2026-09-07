-- Equation52716 → Equation41608
-- Recorded verdict: true
-- Premise: x * y = ((z * (z * x)) * y) * x
-- Conclusion: x * x = y * (x * (z * (y * w)))
-- Original submission SHA-256: 1ed1d8b60b701f31658c63a3d1a00920cd1a07c819771b9c9a58f624c92450ca
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib.Tactic

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ (z ◇ x)) ◇ y) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (x ◇ (z ◇ (y ◇ w)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc2 : forall (q0 q1 q2:G), ((q2 ◇ ((q0 ◇ (q0 ◇ q2)) ◇ q1)) ◇ q1) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ q1) ((h q2 ((q0 ◇ (q0 ◇ q2)) ◇ q1) q0).symm)).symm).trans ((h q1 q2 (q0 ◇ (q0 ◇ q2))).symm)
  have apc3 : forall (q3 q4 q5:G), ((q5 ◇ (q4 ◇ ((q3 ◇ (q3 ◇ q4)) ◇ q5))) ◇ q4) = (q4 ◇ q5):=by
    intro q3 q4 q5
    exact ((cg (fun t => t ◇ q4) (cg (fun t => q5 ◇ t) ((h q4 ((q3 ◇ (q3 ◇ q4)) ◇ q5) q3).symm))).symm).trans (apc2 (q3 ◇ (q3 ◇ q4)) q4 q5)
  have apc4 : forall (q6 q7:G), (((q6 ◇ (q6 ◇ q7)) ◇ q7) ◇ q7) = ((q7 ◇ q7) ◇ ((q6 ◇ (q6 ◇ q7)) ◇ q7)):=by
    intro q6 q7
    exact (((cg (fun t => t ◇ ((q6 ◇ (q6 ◇ q7)) ◇ q7)) (apc3 q6 q7 q7)).symm).trans ((h ((q6 ◇ (q6 ◇ q7)) ◇ q7) q7 q7).symm)).symm
  have apc5 : forall (q8 q9:G), ((q8 ◇ q8) ◇ ((q9 ◇ (q9 ◇ q8)) ◇ q8)) = (q8 ◇ q8):=by
    intro q8 q9
    exact ((apc4 q9 q8).symm).trans ((h q8 q8 q9).symm)
  have apc6 : forall (q6 q7 q8 q9:G), (((q6 ◇ (q6 ◇ q7)) ◇ q7) ◇ q7) = (q7 ◇ q7):=by
    intro q6 q7 q8 q9
    exact (apc4 q6 q7).trans (apc5 q7 q6)
  have apc14 : forall (q10 q11 q12 q13:G), ((((q11 ◇ ((q10 ◇ (q10 ◇ q11)) ◇ q12)) ◇ (q12 ◇ q11)) ◇ q13) ◇ q12) = (q12 ◇ q13):=by
    intro q10 q11 q12 q13
    exact ((cg (fun t => t ◇ q12) (cg (fun t => t ◇ q13) (cg (fun t => (q11 ◇ ((q10 ◇ (q10 ◇ q11)) ◇ q12)) ◇ t) (apc2 q10 q12 q11)))).symm).trans ((h q12 q13 (q11 ◇ ((q10 ◇ (q10 ◇ q11)) ◇ q12))).symm)
  have apc15 : forall (q14 q15:G), (((q14 ◇ q14) ◇ q15) ◇ (q14 ◇ q14)) = ((q14 ◇ q14) ◇ q15):=by
    intro q14 q15
    exact (((cg (fun t => t ◇ (q14 ◇ q14)) (cg (fun t => t ◇ q15) (apc2 q14 (q14 ◇ q14) ((q14 ◇ (q14 ◇ q14)) ◇ q14)))).trans (cg (fun t => t ◇ (q14 ◇ q14)) (cg (fun t => t ◇ q15) (apc5 q14 q14)))).symm).trans (((cg (fun t => t ◇ (q14 ◇ q14)) (cg (fun t => t ◇ q15) (cg (fun t => (((q14 ◇ (q14 ◇ q14)) ◇ q14) ◇ ((q14 ◇ (q14 ◇ ((q14 ◇ (q14 ◇ q14)) ◇ q14))) ◇ (q14 ◇ q14))) ◇ t) (apc5 q14 q14)))).symm).trans (apc14 q14 ((q14 ◇ (q14 ◇ q14)) ◇ q14) (q14 ◇ q14) q15))
  have apc16 : forall (q16:G), ((q16 ◇ q16) ◇ (q16 ◇ q16)) = (q16 ◇ q16):=by
    intro q16
    exact (((cg (fun t => t ◇ (q16 ◇ q16)) (apc5 q16 q16)).symm).trans (apc15 q16 ((q16 ◇ (q16 ◇ q16)) ◇ q16))).trans (apc5 q16 q16)
  have apc17 : forall (q17 q18:G), (((q17 ◇ q17) ◇ ((q17 ◇ q17) ◇ q18)) ◇ q18) = (q18 ◇ (q17 ◇ q17)):=by
    intro q17 q18
    exact ((cg (fun t => t ◇ q18) (apc15 q17 ((q17 ◇ q17) ◇ q18))).symm).trans ((h q18 (q17 ◇ q17) (q17 ◇ q17)).symm)
  have apc18 : forall (q19 q20:G), ((q20 ◇ (q19 ◇ q19)) ◇ q20) = (q20 ◇ q20):=by
    intro q19 q20
    exact ((cg (fun t => t ◇ q20) (apc17 q19 q20)).symm).trans ((h q20 q20 (q19 ◇ q19)).symm)
  have apc19 : forall (q21:G), ((q21 ◇ q21) ◇ q21) = (q21 ◇ q21):=by
    intro q21
    exact ((cg (fun t => t ◇ q21) (apc18 q21 q21)).symm).trans ((h q21 q21 q21).symm)
  have apc21 : forall (q22 q23:G), ((q23 ◇ q23) ◇ (q22 ◇ q22)) = (q23 ◇ q23):=by
    intro q22 q23
    exact (((apc16 q23).symm).trans (((apc18 q22 (q23 ◇ q23)).symm).trans (apc15 q23 (q22 ◇ q22)))).symm
  have apc22 : forall (q24 q25:G), (q25 ◇ q25) = (q24 ◇ q24):=by
    intro q24 q25
    exact ((((cg (fun t => t ◇ (q24 ◇ q24)) (cg (fun t => t ◇ (q24 ◇ q24)) (apc21 q25 q25))).trans (cg (fun t => t ◇ (q24 ◇ q24)) (apc21 q24 q25))).trans (apc21 q24 q25)).symm).trans ((((cg (fun t => t ◇ (q24 ◇ q24)) (cg (fun t => t ◇ (q24 ◇ q24)) (cg (fun t => (q25 ◇ q25) ◇ t) (apc21 q24 q25)))).symm).trans (apc6 (q25 ◇ q25) (q24 ◇ q24) q24 q24)).trans (apc21 q24 q24))
  have apc23 : forall (q26 q27:G), ((q26 ◇ q26) ◇ q27) = (q27 ◇ q27):=by
    intro q26 q27
    exact ((cg (fun t => t ◇ q27) (apc22 q26 q27)).symm).trans (apc19 q27)
  have apc24 : forall (q28 q29:G), (q28 ◇ q29) = (q28 ◇ q28):=by
    intro q28 q29
    exact ((((((cg (fun t => t ◇ q28) (cg (fun t => t ◇ q29) (cg (fun t => t ◇ ((q28 ◇ q28) ◇ q28)) (apc23 q28 q28)))).trans (cg (fun t => t ◇ q28) (cg (fun t => t ◇ q29) (cg (fun t => (q28 ◇ q28) ◇ t) (apc23 q28 q28))))).trans (cg (fun t => t ◇ q28) (apc23 (q28 ◇ q28) q29))).trans (apc23 q29 q28)).symm).trans (((cg (fun t => t ◇ q28) (cg (fun t => t ◇ q29) (apc23 q28 ((q28 ◇ q28) ◇ q28)))).symm).trans ((h q28 q29 (q28 ◇ q28)).symm))).symm
  exact (calc
    (x ◇ x) = (y ◇ y):=apc22 y x
    _ = (y ◇ (x ◇ (z ◇ (y ◇ w)))):=(apc24 y (x ◇ (z ◇ (y ◇ w)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52716_to_41608 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52716_to_41608
