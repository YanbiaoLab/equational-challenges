-- Equation46280 → Equation3567
-- Recorded verdict: true
-- Premise: x * y = (y * x) * (y * (x * z))
-- Conclusion: x * y = y * ((z * x) * z)
-- Original submission SHA-256: f5df941dda4aafeaa0cf65ee25612b54d673f3d6400ee9cdd66278c52ff2766b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ x) ◇ (y ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ ((z ◇ x) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), (((q1 ◇ q0) ◇ q1) ◇ (q0 ◇ q1)) = (q1 ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => ((q1 ◇ q0) ◇ q1) ◇ t) ((h q0 q1 q0).symm)).symm).trans ((h q1 (q1 ◇ q0) (q0 ◇ q0)).symm)
  have apc1 : forall (x y z:G), ((y ◇ x) ◇ (y ◇ (x ◇ z))) = ((y ◇ x) ◇ (y ◇ (x ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc2 : forall (x y z:G), ((y ◇ x) ◇ (y ◇ (x ◇ x))) = (x ◇ y):=by
    intro x y z
    exact ((h x y x).trans (apc1 x y x)).symm
  have apc3 : forall (q0 q2 q3:G), ((q3 ◇ (q2 ◇ q0)) ◇ (q3 ◇ (q0 ◇ q2))) = ((q2 ◇ q0) ◇ q3):=by
    intro q0 q2 q3
    exact ((cg (fun t => (q3 ◇ (q2 ◇ q0)) ◇ t) (cg (fun t => q3 ◇ t) ((h q0 q2 q0).symm))).symm).trans ((h (q2 ◇ q0) q3 (q2 ◇ (q0 ◇ q0))).symm)
  have apc4 : forall (q4:G), ((q4 ◇ q4) ◇ ((q4 ◇ q4) ◇ q4)) = ((q4 ◇ q4) ◇ q4):=by
    intro q4
    exact (((apc3 q4 q4 q4).symm).trans (((cg (fun t => t ◇ (q4 ◇ (q4 ◇ q4))) (apc0 q4 q4)).symm).trans (apc0 q4 (q4 ◇ q4)))).symm
  have apc5 : forall (q5:G), ((q5 ◇ (q5 ◇ q5)) ◇ (q5 ◇ q5)) = ((q5 ◇ q5) ◇ q5):=by
    intro q5
    exact ((((cg (fun t => t ◇ ((q5 ◇ q5) ◇ q5)) (apc2 q5 q5 ((q5 ◇ q5) ◇ (q5 ◇ (q5 ◇ q5))))).trans (apc4 q5)).symm).trans (((cg (fun t => ((q5 ◇ q5) ◇ (q5 ◇ (q5 ◇ q5))) ◇ t) (apc4 q5)).symm).trans (apc3 (q5 ◇ q5) q5 (q5 ◇ q5)))).symm
  have apc6 : forall (q6:G), (((q6 ◇ q6) ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) = (q6 ◇ q6):=by
    intro q6
    exact ((cg (fun t => ((q6 ◇ q6) ◇ q6) ◇ t) (apc5 q6)).symm).trans ((((cg (fun t => t ◇ ((q6 ◇ (q6 ◇ q6)) ◇ (q6 ◇ q6))) (apc5 q6)).symm).trans (apc3 q6 q6 (q6 ◇ (q6 ◇ q6)))).trans (apc2 q6 q6 ((q6 ◇ q6) ◇ (q6 ◇ (q6 ◇ q6)))))
  have apc7 : forall (q7:G), ((q7 ◇ q7) ◇ ((q7 ◇ q7) ◇ (q7 ◇ q7))) = ((q7 ◇ q7) ◇ (q7 ◇ q7)):=by
    intro q7
    exact (((apc6 (q7 ◇ q7)).symm).trans (apc3 q7 q7 ((q7 ◇ q7) ◇ (q7 ◇ q7)))).symm
  have apc8 : forall (q8 q9:G), ((((q9 ◇ q8) ◇ q9) ◇ q8) ◇ (q9 ◇ (q9 ◇ q8))) = (q8 ◇ ((q9 ◇ q8) ◇ q9)):=by
    intro q8 q9
    exact ((cg (fun t => (((q9 ◇ q8) ◇ q9) ◇ q8) ◇ t) (apc0 q8 q9)).symm).trans ((h q8 ((q9 ◇ q8) ◇ q9) q9).symm)
  have apc10 : forall (q10:G), (((q10 ◇ q10) ◇ (q10 ◇ q10)) ◇ (q10 ◇ q10)) = ((q10 ◇ q10) ◇ (q10 ◇ q10)):=by
    intro q10
    exact (((((cg (fun t => t ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10))) (apc0 (q10 ◇ q10) (q10 ◇ q10))).trans (cg (fun t => t ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10))) (apc7 q10))).trans (apc3 q10 q10 (q10 ◇ q10))).symm).trans ((((cg (fun t => ((((q10 ◇ q10) ◇ (q10 ◇ q10)) ◇ (q10 ◇ q10)) ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10))) ◇ t) (apc7 q10)).symm).trans (apc0 (q10 ◇ q10) ((q10 ◇ q10) ◇ (q10 ◇ q10)))).trans (apc4 (q10 ◇ q10)))).symm
  have apc11 : forall (q11 q12 q13:G), ((q11 ◇ q13) ◇ ((q13 ◇ q11) ◇ ((q11 ◇ q12) ◇ q13))) = ((q13 ◇ (q11 ◇ q12)) ◇ (q13 ◇ q11)):=by
    intro q11 q12 q13
    exact ((cg (fun t => t ◇ ((q13 ◇ q11) ◇ ((q11 ◇ q12) ◇ q13))) ((h q11 q13 q12).symm)).symm).trans (apc3 (q11 ◇ q12) q13 (q13 ◇ q11))
  have apc12 : forall (q14:G), (((q14 ◇ q14) ◇ (q14 ◇ q14)) ◇ ((q14 ◇ q14) ◇ q14)) = ((q14 ◇ q14) ◇ q14):=by
    intro q14
    exact (((apc3 q14 q14 q14).symm).trans (((cg (fun t => (q14 ◇ (q14 ◇ q14)) ◇ t) (apc2 q14 (q14 ◇ q14) q14)).symm).trans (apc11 q14 q14 (q14 ◇ q14)))).symm
  have apc13 : forall (q15:G), ((q15 ◇ q15) ◇ (q15 ◇ q15)) = ((q15 ◇ q15) ◇ q15):=by
    intro q15
    exact ((((cg (fun t => t ◇ ((q15 ◇ q15) ◇ q15)) (apc10 q15)).trans (apc12 q15)).symm).trans ((((cg (fun t => (((q15 ◇ q15) ◇ (q15 ◇ q15)) ◇ (q15 ◇ q15)) ◇ t) (apc12 q15)).symm).trans ((h (q15 ◇ q15) ((q15 ◇ q15) ◇ (q15 ◇ q15)) q15).symm)).trans (apc7 q15))).symm
  have apc14 : forall (q16:G), (q16 ◇ (q16 ◇ q16)) = (q16 ◇ q16):=by
    intro q16
    exact (((apc6 q16).symm).trans (((cg (fun t => ((q16 ◇ q16) ◇ q16) ◇ t) (apc13 q16)).symm).trans ((h q16 (q16 ◇ q16) q16).symm))).symm
  have apc15 : forall (q17:G), ((q17 ◇ q17) ◇ q17) = (q17 ◇ q17):=by
    intro q17
    exact (((((cg (fun t => ((q17 ◇ q17) ◇ q17) ◇ t) (cg (fun t => (q17 ◇ q17) ◇ t) (apc13 q17))).trans (cg (fun t => ((q17 ◇ q17) ◇ q17) ◇ t) (apc4 q17))).trans (apc6 q17)).symm).trans ((((cg (fun t => t ◇ ((q17 ◇ q17) ◇ ((q17 ◇ q17) ◇ (q17 ◇ q17)))) (apc13 q17)).symm).trans (apc2 (q17 ◇ q17) (q17 ◇ q17) q17)).trans (apc13 q17))).symm
  have apc16 : forall (q17 q4:G), ((q4 ◇ q4) ◇ (q4 ◇ q4)) = (q4 ◇ q4):=by
    intro q17 q4
    exact ((cg (fun t => (q4 ◇ q4) ◇ t) (apc15 q4)).symm).trans ((apc4 q4).trans (apc15 q4))
  have apc17 : forall (q18 q19:G), ((q18 ◇ q18) ◇ ((q18 ◇ q18) ◇ (q18 ◇ q19))) = (q18 ◇ q18):=by
    intro q18 q19
    exact (((cg (fun t => t ◇ ((q18 ◇ q18) ◇ (q18 ◇ q19))) (apc15 q18)).symm).trans ((h q18 (q18 ◇ q18) q19).symm)).trans (apc14 q18)
  have apc22 : forall (q20 q21:G), (((q20 ◇ q20) ◇ (q20 ◇ q21)) ◇ (q20 ◇ q20)) = (q20 ◇ q20):=by
    intro q20 q21
    exact (((((((cg (fun t => t ◇ ((q20 ◇ q20) ◇ ((q20 ◇ q20) ◇ ((q20 ◇ q20) ◇ (q20 ◇ q21))))) (cg (fun t => t ◇ ((q20 ◇ q20) ◇ (q20 ◇ q21))) (apc16 ((q20 ◇ q20) ◇ (q20 ◇ q20)) q20))).trans (cg (fun t => ((q20 ◇ q20) ◇ ((q20 ◇ q20) ◇ (q20 ◇ q21))) ◇ t) (cg (fun t => (q20 ◇ q20) ◇ t) (apc17 q20 q21)))).trans (cg (fun t => ((q20 ◇ q20) ◇ ((q20 ◇ q20) ◇ (q20 ◇ q21))) ◇ t) (apc16 ((q20 ◇ q20) ◇ (q20 ◇ q20)) q20))).trans (cg (fun t => t ◇ (q20 ◇ q20)) (apc17 q20 q21))).trans (apc16 ((q20 ◇ q20) ◇ (q20 ◇ q20)) q20)).symm).trans ((((cg (fun t => t ◇ ((q20 ◇ q20) ◇ ((q20 ◇ q20) ◇ ((q20 ◇ q20) ◇ (q20 ◇ q21))))) (cg (fun t => t ◇ ((q20 ◇ q20) ◇ (q20 ◇ q21))) (cg (fun t => t ◇ (q20 ◇ q20)) (apc17 q20 q21)))).symm).trans (apc8 ((q20 ◇ q20) ◇ (q20 ◇ q21)) (q20 ◇ q20))).trans ((cg (fun t => ((q20 ◇ q20) ◇ (q20 ◇ q21)) ◇ t) (cg (fun t => t ◇ (q20 ◇ q20)) (apc17 q20 q21))).trans (cg (fun t => ((q20 ◇ q20) ◇ (q20 ◇ q21)) ◇ t) (apc16 ((q20 ◇ q20) ◇ (q20 ◇ q20)) q20))))).symm
  have apc23 : forall (q22 q23:G), ((q22 ◇ q23) ◇ (q22 ◇ q22)) = (q22 ◇ q22):=by
    intro q22 q23
    exact ((((cg (fun t => ((q22 ◇ q22) ◇ (q22 ◇ q23)) ◇ t) (apc17 q22 q23)).trans (apc22 q22 q23)).symm).trans ((((cg (fun t => t ◇ ((q22 ◇ q22) ◇ ((q22 ◇ q22) ◇ (q22 ◇ q23)))) (cg (fun t => t ◇ (q22 ◇ q23)) (apc22 q22 q23))).symm).trans (apc8 (q22 ◇ q23) (q22 ◇ q22))).trans (cg (fun t => (q22 ◇ q23) ◇ t) (apc22 q22 q23)))).symm
  have apc24 : forall (q24 q25:G), ((q24 ◇ q24) ◇ (q24 ◇ q25)) = (q24 ◇ q24):=by
    intro q24 q25
    exact (((((cg (fun t => (q24 ◇ q24) ◇ t) (cg (fun t => (q24 ◇ q25) ◇ t) (apc23 q24 q24))).trans (cg (fun t => (q24 ◇ q24) ◇ t) (apc23 q24 q25))).trans (apc23 q24 q24)).symm).trans (((cg (fun t => t ◇ ((q24 ◇ q25) ◇ ((q24 ◇ q24) ◇ (q24 ◇ q24)))) (apc23 q24 q25)).symm).trans (apc2 (q24 ◇ q24) (q24 ◇ q25) q24))).symm
  have apc25 : forall (q26 q27:G), ((q26 ◇ q27) ◇ (q26 ◇ q27)) = (q26 ◇ (q26 ◇ q27)):=by
    intro q26 q27
    exact ((apc23 (q26 ◇ q27) q26).symm).trans ((h q26 (q26 ◇ q27) q27).symm)
  have apc27 : forall (q28 q29:G), (q28 ◇ (q28 ◇ (q28 ◇ q29))) = (q28 ◇ (q28 ◇ q29)):=by
    intro q28 q29
    exact (((cg (fun t => (q28 ◇ (q28 ◇ q29)) ◇ t) (apc25 q28 q29)).trans (apc25 q28 (q28 ◇ q29))).symm).trans ((((cg (fun t => t ◇ ((q28 ◇ q29) ◇ (q28 ◇ q29))) (apc25 q28 q29)).symm).trans (apc23 (q28 ◇ q29) (q28 ◇ q29))).trans (apc25 q28 q29))
  have apc28 : forall (q30 q31:G), (q31 ◇ (q31 ◇ (q30 ◇ q30))) = ((q30 ◇ q30) ◇ q31):=by
    intro q30 q31
    exact ((apc25 q31 (q30 ◇ q30)).symm).trans (apc3 q30 q30 q31)
  have apc29 : forall (q32 q33:G), ((q33 ◇ (q33 ◇ q32)) ◇ q33) = (q33 ◇ (q33 ◇ q32)):=by
    intro q32 q33
    exact (((((((cg (fun t => (q33 ◇ (q33 ◇ q32)) ◇ t) (cg (fun t => q33 ◇ t) (apc25 q33 (q33 ◇ q32)))).trans (cg (fun t => (q33 ◇ (q33 ◇ q32)) ◇ t) (cg (fun t => q33 ◇ t) (apc27 q33 q32)))).trans (cg (fun t => (q33 ◇ (q33 ◇ q32)) ◇ t) (apc27 q33 q32))).trans (apc25 q33 (q33 ◇ q32))).trans (apc27 q33 q32)).symm).trans (((cg (fun t => t ◇ (q33 ◇ ((q33 ◇ (q33 ◇ q32)) ◇ (q33 ◇ (q33 ◇ q32))))) (apc27 q33 q32)).symm).trans (apc2 (q33 ◇ (q33 ◇ q32)) q33 q32))).symm
  have apc30 : forall (q34 q35:G), (q35 ◇ (q35 ◇ q34)) = (q35 ◇ q35):=by
    intro q34 q35
    exact ((((cg (fun t => (q35 ◇ (q35 ◇ q34)) ◇ t) (apc23 q35 (q35 ◇ q34))).trans (apc23 q35 (q35 ◇ q34))).symm).trans ((((cg (fun t => t ◇ ((q35 ◇ (q35 ◇ q34)) ◇ (q35 ◇ q35))) (apc29 q34 q35)).symm).trans (apc2 q35 (q35 ◇ (q35 ◇ q34)) q34)).trans (apc27 q35 q34))).symm
  have apc31 : forall (q30 q31 q34 q35:G), ((q30 ◇ q30) ◇ q31) = (q31 ◇ q31):=by
    intro q30 q31 q34 q35
    exact (((apc30 (q30 ◇ q30) q31).symm).trans (apc28 q30 q31)).symm
  have apc35 : forall (q36 q37:G), (q37 ◇ (q36 ◇ q36)) = (q37 ◇ q37):=by
    intro q36 q37
    exact (((((cg (fun t => t ◇ ((q37 ◇ q37) ◇ (q37 ◇ q37))) (apc31 q36 q37 ((q36 ◇ q36) ◇ q37) ((q36 ◇ q36) ◇ q37))).trans (cg (fun t => (q37 ◇ q37) ◇ t) (apc23 q37 q37))).trans (apc23 q37 q37)).symm).trans (((cg (fun t => ((q36 ◇ q36) ◇ q37) ◇ t) (apc31 q36 (q37 ◇ q37) q36 q36)).symm).trans (apc2 q37 (q36 ◇ q36) q36))).symm
  have apc36 : forall (q38 q39:G), (q39 ◇ q38) = (q38 ◇ q38):=by
    intro q38 q39
    exact (((apc23 q38 q39).symm).trans (((cg (fun t => (q38 ◇ q39) ◇ t) (apc35 q39 q38)).symm).trans ((h q39 q38 q39).symm))).symm
  have apc37 : forall (q40 q41:G), (q40 ◇ q41) = (q40 ◇ q40):=by
    intro q40 q41
    exact (((((cg (fun t => t ◇ ((q40 ◇ q40) ◇ (q40 ◇ q40))) (apc36 q40 q41)).trans (apc35 (q40 ◇ q40) (q40 ◇ q40))).trans (apc24 q40 q40)).symm).trans (((cg (fun t => (q41 ◇ q40) ◇ t) (apc36 (q40 ◇ q40) q41)).symm).trans ((h q40 q41 q40).symm))).symm
  exact (calc
    (x ◇ y) = (y ◇ y):=apc36 y x
    _ = (y ◇ ((z ◇ x) ◇ z)):=(apc37 y ((z ◇ x) ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46280_to_3567 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46280_to_3567
