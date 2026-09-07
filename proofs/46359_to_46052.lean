-- Equation46359 → Equation46052
-- Recorded verdict: true
-- Premise: x * y = (y * z) * (y * (x * x))
-- Conclusion: x * x = (y * z) * (x * (w * x))
-- Original submission SHA-256: 6045b3afedac84c204b39bb6e91b2f30bd89d8409f8b732734639830a929c909
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ z) ◇ (y ◇ (x ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = (y ◇ z) ◇ (x ◇ (w ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 q3:G), ((q2 ◇ q3) ◇ (q2 ◇ (q0 ◇ q1))) = ((q1 ◇ (q0 ◇ q0)) ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (q2 ◇ q3) ◇ t) (cg (fun t => q2 ◇ t) ((h q0 q1 (q0 ◇ q0)).symm))).symm).trans ((h (q1 ◇ (q0 ◇ q0)) q2 q3).symm)
  have apc1 : forall (q0 q1 q4 q5:G), ((q0 ◇ q1) ◇ ((q1 ◇ q4) ◇ (q5 ◇ q5))) = (q5 ◇ (q1 ◇ q4)):=by
    intro q0 q1 q4 q5
    exact ((cg (fun t => t ◇ ((q1 ◇ q4) ◇ (q5 ◇ q5))) ((h q0 q1 q4).symm)).symm).trans ((h q5 (q1 ◇ q4) (q1 ◇ (q0 ◇ q0))).symm)
  have apc2 : forall (q6 q7 q8:G), ((q7 ◇ q8) ◇ (q6 ◇ (q6 ◇ q6))) = ((q6 ◇ q6) ◇ (q8 ◇ q6)):=by
    intro q6 q7 q8
    exact ((cg (fun t => (q7 ◇ q8) ◇ t) (apc1 q8 q6 q6 q6)).symm).trans (apc1 q7 q8 q6 (q6 ◇ q6))
  have apc3 : forall (q9 q10:G), ((q9 ◇ q9) ◇ (q10 ◇ q9)) = (q9 ◇ q9):=by
    intro q9 q10
    exact ((apc2 q9 q9 q10).symm).trans ((h q9 q9 q10).symm)
  have apc4 : forall (q6 q7 q8 q9 q10:G), ((q7 ◇ q8) ◇ (q6 ◇ (q6 ◇ q6))) = (q6 ◇ q6):=by
    intro q6 q7 q8 q9 q10
    exact (apc2 q6 q7 q8).trans (apc3 q6 q8)
  have apc6 : forall (q11 q12 q13:G), ((q12 ◇ q13) ◇ (q11 ◇ q11)) = (q11 ◇ q11):=by
    intro q11 q12 q13
    exact ((cg (fun t => (q12 ◇ q13) ◇ t) (apc3 q11 q11)).symm).trans ((((cg (fun t => (q12 ◇ q13) ◇ t) (cg (fun t => (q11 ◇ q11) ◇ t) (apc3 q11 q11))).symm).trans (apc4 (q11 ◇ q11) q12 q13 q11 q11)).trans (apc3 q11 q11))
  have apc7 : forall (q14:G), (q14 ◇ (q14 ◇ q14)) = (q14 ◇ q14):=by
    intro q14
    exact (((apc3 q14 q14).symm).trans (((apc3 (q14 ◇ q14) (q14 ◇ q14)).symm).trans ((h q14 (q14 ◇ q14) (q14 ◇ q14)).symm))).symm
  have apc11 : forall (q15 q16:G), ((q15 ◇ q15) ◇ q16) = (q15 ◇ q16):=by
    intro q15 q16
    exact (((apc0 q15 q15 q16 q16).trans (cg (fun t => t ◇ q16) (apc7 q15))).symm).trans (((cg (fun t => t ◇ (q16 ◇ (q15 ◇ q15))) (apc7 q16)).symm).trans ((h q15 q16 (q16 ◇ q16)).symm))
  have apc13 : forall (q17 q18:G), (q18 ◇ (q18 ◇ (q17 ◇ q17))) = (q17 ◇ q18):=by
    intro q17 q18
    exact ((apc11 q18 (q18 ◇ (q17 ◇ q17))).symm).trans ((h q17 q18 q18).symm)
  have apc14 : forall (q19 q20 q21:G), ((q19 ◇ q21) ◇ (q21 ◇ (q20 ◇ q20))) = (q20 ◇ q21):=by
    intro q19 q20 q21
    exact ((cg (fun t => t ◇ (q21 ◇ (q20 ◇ q20))) (apc13 q19 q21)).symm).trans ((h q20 q21 (q21 ◇ (q19 ◇ q19))).symm)
  have apc15 : forall (q22 q23 q24:G), ((q23 ◇ q24) ◇ (q22 ◇ q23)) = (q23 ◇ q23):=by
    intro q22 q23 q24
    exact (((cg (fun t => (q23 ◇ q24) ◇ t) (apc13 q22 q23)).symm).trans (apc0 q23 (q22 ◇ q22) q23 q24)).trans ((cg (fun t => t ◇ q23) (apc6 q23 q22 q22)).trans (apc11 q23 q23))
  have apc16 : forall (q25 q26 q27:G), ((q25 ◇ q27) ◇ (q26 ◇ (q25 ◇ q25))) = (q25 ◇ q25):=by
    intro q25 q26 q27
    exact (((cg (fun t => t ◇ (q26 ◇ (q25 ◇ q25))) (apc11 q25 q27)).symm).trans (apc15 q26 (q25 ◇ q25) q27)).trans (apc6 q25 q25 q25)
  have apc19 : forall (q28 q29 q30:G), ((q28 ◇ q30) ◇ (q29 ◇ q30)) = (q30 ◇ q30):=by
    intro q28 q29 q30
    exact ((cg (fun t => t ◇ (q29 ◇ q30)) (apc13 q28 q30)).symm).trans (apc15 q29 q30 (q30 ◇ (q28 ◇ q28)))
  have apc20 : forall (q31 q32 q33:G), (q33 ◇ (q32 ◇ (q31 ◇ q31))) = (q33 ◇ q33):=by
    intro q31 q32 q33
    exact ((((cg (fun t => (q31 ◇ q32) ◇ t) (apc6 q33 q32 (q31 ◇ q31))).trans (apc6 q33 q31 q32)).symm).trans (((cg (fun t => t ◇ ((q32 ◇ (q31 ◇ q31)) ◇ (q33 ◇ q33))) ((h q31 q32 q31).symm)).symm).trans (apc14 (q32 ◇ q31) q33 (q32 ◇ (q31 ◇ q31))))).symm
  have apc21 : forall (q31 q32 q33 q25 q26 q27:G), (q27 ◇ q27) = (q25 ◇ q25):=by
    intro q31 q32 q33 q25 q26 q27
    exact ((apc19 q25 q25 q27).symm).trans (((apc20 q25 q26 (q25 ◇ q27)).symm).trans (apc16 q25 q26 q27))
  have apc22 : forall (q34 q35 q36 q37:G), ((q36 ◇ q37) ◇ (q34 ◇ q35)) = (q34 ◇ q35):=by
    intro q34 q35 q36 q37
    exact ((((cg (fun t => (q36 ◇ q37) ◇ t) (apc0 q34 q34 q35 (q34 ◇ q34))).trans (cg (fun t => (q36 ◇ q37) ◇ t) (cg (fun t => t ◇ q35) (apc7 q34)))).trans (cg (fun t => (q36 ◇ q37) ◇ t) (apc11 q34 q35))).symm).trans ((((cg (fun t => (q36 ◇ q37) ◇ t) (apc20 q34 q35 (q35 ◇ (q34 ◇ q34)))).symm).trans (apc6 (q35 ◇ (q34 ◇ q34)) q36 q37)).trans (((apc0 q34 q34 q35 (q34 ◇ q34)).trans (cg (fun t => t ◇ q35) (apc7 q34))).trans (apc11 q34 q35)))
  have apc23 : forall (q38 q39 q40 q41:G), (q41 ◇ (q40 ◇ (q38 ◇ q39))) = (q41 ◇ q41):=by
    intro q38 q39 q40 q41
    exact ((((cg (fun t => ((q39 ◇ (q38 ◇ q38)) ◇ q40) ◇ t) (apc22 q41 q41 q40 (q38 ◇ q39))).trans (apc22 q41 q41 (q39 ◇ (q38 ◇ q38)) q40)).symm).trans (((cg (fun t => t ◇ ((q40 ◇ (q38 ◇ q39)) ◇ (q41 ◇ q41))) (apc0 q38 q39 q40 q38)).symm).trans (apc14 (q40 ◇ q38) q41 (q40 ◇ (q38 ◇ q39))))).symm
  have apc24 : forall (q42 q43 q44 q45:G), ((q42 ◇ q43) ◇ q44) = (q44 ◇ q44):=by
    intro q42 q43 q44 q45
    exact (((apc22 q44 q44 q44 q45).symm).trans (((cg (fun t => (q44 ◇ q45) ◇ t) (apc23 q42 q43 (q42 ◇ q43) q44)).symm).trans ((h (q42 ◇ q43) q44 q45).symm))).symm
  have apc25 : forall (q46 q47 q48:G), ((q46 ◇ q47) ◇ (q46 ◇ q47)) = (q48 ◇ q48):=by
    intro q46 q47 q48
    exact ((apc24 q46 q47 (q46 ◇ q47) q46).symm).trans (apc21 q46 q46 q46 q48 q46 (q46 ◇ q47))
  have apc29 : forall (q49 q50 q51 q52 q53:G), ((q49 ◇ q50) ◇ (q49 ◇ q50)) = (q49 ◇ q49):=by
    intro q49 q50 q51 q52 q53
    exact ((apc23 q51 q51 q49 (q49 ◇ q50)).symm).trans ((((cg (fun t => (q49 ◇ q50) ◇ t) (cg (fun t => q49 ◇ t) (apc25 q52 q53 q51))).symm).trans ((h (q52 ◇ q53) q49 q50).symm)).trans (apc24 q52 q53 q49 ((q52 ◇ q53) ◇ q49)))
  have apc35 : forall (q0 q1 q4 q5 q11 q12 q13:G), (q5 ◇ (q1 ◇ q4)) = (q5 ◇ q5):=by
    intro q0 q1 q4 q5 q11 q12 q13
    exact ((((cg (fun t => (q0 ◇ q1) ◇ t) (apc6 q5 q1 q4)).trans (apc6 q5 q0 q1)).symm).trans (apc1 q0 q1 q4 q5)).symm
  exact (calc
    (x ◇ x) = (x ◇ x):=rfl
    _ = ((y ◇ z) ◇ (x ◇ (w ◇ x))):=(((cg (fun t => (y ◇ z) ◇ t) (apc35 (x ◇ (w ◇ x)) w x x (x ◇ (w ◇ x)) (x ◇ (w ◇ x)) (x ◇ (w ◇ x)))).trans (apc24 y z (x ◇ x) ((y ◇ z) ◇ (x ◇ x)))).trans (apc29 x x ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46359_to_46052 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46359_to_46052
