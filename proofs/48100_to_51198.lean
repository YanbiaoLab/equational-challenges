-- Equation48100 → Equation51198
-- Recorded verdict: true
-- Premise: x * y = (y * (z * x)) * (y * x)
-- Conclusion: x * x = ((x * y) * (x * z)) * y
-- Original submission SHA-256: e324c7e731ccafff371faa2d86cd133c7a37a8b2acf20f61a0b711a9a5774fe1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ (z ◇ x)) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = ((x ◇ y) ◇ (x ◇ z)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((y ◇ (z ◇ x)) ◇ (y ◇ x)) = ((y ◇ (x ◇ x)) ◇ (y ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (x y z:G), ((y ◇ (x ◇ x)) ◇ (y ◇ x)) = (x ◇ y):=by
    intro x y z
    exact ((h x y x).trans (apc0 x y x)).symm
  have apc2 : forall (q0 q1 q2:G), ((q2 ◇ (q0 ◇ q1)) ◇ (q2 ◇ (q1 ◇ q0))) = ((q1 ◇ q0) ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q2 ◇ (q1 ◇ q0))) (cg (fun t => q2 ◇ t) ((h q0 q1 q0).symm))).symm).trans ((h (q1 ◇ q0) q2 (q1 ◇ (q0 ◇ q0))).symm)
  have apc5 : forall (q3 q4 q5:G), ((q5 ◇ q4) ◇ ((q4 ◇ (q3 ◇ q5)) ◇ (q5 ◇ q4))) = ((q5 ◇ q4) ◇ (q4 ◇ (q3 ◇ q5))):=by
    intro q3 q4 q5
    exact ((cg (fun t => t ◇ ((q4 ◇ (q3 ◇ q5)) ◇ (q5 ◇ q4))) ((h q5 q4 q3).symm)).symm).trans (apc2 q4 q5 (q4 ◇ (q3 ◇ q5)))
  have apc6 : forall (q6 q7:G), ((q7 ◇ q7) ◇ (q7 ◇ (q6 ◇ q7))) = ((q7 ◇ q7) ◇ (q7 ◇ q7)):=by
    intro q6 q7
    exact (((cg (fun t => (q7 ◇ q7) ◇ t) ((h q7 q7 q6).symm)).symm).trans (apc5 q6 q7 q7)).symm
  have apc11 : forall (q0 q1 q8 q9:G), (((q1 ◇ (q8 ◇ q0)) ◇ (q9 ◇ (q1 ◇ q0))) ◇ (q0 ◇ q1)) = ((q1 ◇ q0) ◇ (q1 ◇ (q8 ◇ q0))):=by
    intro q0 q1 q8 q9
    exact ((cg (fun t => ((q1 ◇ (q8 ◇ q0)) ◇ (q9 ◇ (q1 ◇ q0))) ◇ t) ((h q0 q1 q8).symm)).symm).trans ((h (q1 ◇ q0) (q1 ◇ (q8 ◇ q0)) q9).symm)
  have apc12 : forall (q10:G), (((q10 ◇ q10) ◇ q10) ◇ (q10 ◇ q10)) = ((q10 ◇ q10) ◇ (q10 ◇ q10)):=by
    intro q10
    exact (((cg (fun t => t ◇ (q10 ◇ q10)) (apc2 q10 q10 q10)).symm).trans (apc11 q10 q10 q10 q10)).trans (apc6 q10 q10)
  have apc13 : forall (q11:G), ((q11 ◇ q11) ◇ ((q11 ◇ q11) ◇ q11)) = ((q11 ◇ q11) ◇ (q11 ◇ q11)):=by
    intro q11
    exact ((((cg (fun t => ((q11 ◇ q11) ◇ (q11 ◇ q11)) ◇ t) (apc12 q11)).trans (apc2 q11 q11 (q11 ◇ q11))).symm).trans (((cg (fun t => t ◇ (((q11 ◇ q11) ◇ q11) ◇ (q11 ◇ q11))) (apc12 q11)).symm).trans (apc2 q11 q11 ((q11 ◇ q11) ◇ q11)))).symm
  have apc14 : forall (q12:G), ((q12 ◇ q12) ◇ (q12 ◇ q12)) = (q12 ◇ q12):=by
    intro q12
    exact (((cg (fun t => ((q12 ◇ q12) ◇ (q12 ◇ q12)) ◇ t) (apc6 q12 q12)).trans (apc2 q12 q12 (q12 ◇ q12))).symm).trans ((((cg (fun t => t ◇ ((q12 ◇ q12) ◇ (q12 ◇ (q12 ◇ q12)))) (apc13 q12)).symm).trans (apc2 (q12 ◇ q12) q12 (q12 ◇ q12))).trans (apc1 q12 q12 ((q12 ◇ (q12 ◇ q12)) ◇ (q12 ◇ q12))))
  have apc16 : forall (q6 q7 q12:G), ((q7 ◇ q7) ◇ (q7 ◇ (q6 ◇ q7))) = (q7 ◇ q7):=by
    intro q6 q7 q12
    exact (apc6 q6 q7).trans (apc14 q7)
  have apc18 : forall (q11 q12:G), ((q11 ◇ q11) ◇ ((q11 ◇ q11) ◇ q11)) = (q11 ◇ q11):=by
    intro q11 q12
    exact (apc13 q11).trans (apc14 q11)
  have apc19 : forall (q13:G), (q13 ◇ (q13 ◇ q13)) = (q13 ◇ q13):=by
    intro q13
    exact (((apc18 q13 ((q13 ◇ q13) ◇ ((q13 ◇ q13) ◇ q13))).symm).trans (((cg (fun t => t ◇ ((q13 ◇ q13) ◇ q13)) (apc18 q13 q13)).symm).trans ((h q13 (q13 ◇ q13) (q13 ◇ q13)).symm))).symm
  have apc20 : forall (q14:G), ((q14 ◇ q14) ◇ q14) = (q14 ◇ q14):=by
    intro q14
    exact (((((cg (fun t => t ◇ (q14 ◇ q14)) (cg (fun t => q14 ◇ t) (apc14 q14))).trans (cg (fun t => t ◇ (q14 ◇ q14)) (apc19 q14))).trans (apc14 q14)).symm).trans (((cg (fun t => (q14 ◇ ((q14 ◇ q14) ◇ (q14 ◇ q14))) ◇ t) (apc19 q14)).symm).trans (apc1 (q14 ◇ q14) q14 q14))).symm
  have apc21 : forall (q15 q16:G), (((q15 ◇ q15) ◇ q16) ◇ ((q15 ◇ q15) ◇ q16)) = ((q15 ◇ q15) ◇ q16):=by
    intro q15 q16
    exact ((cg (fun t => ((q15 ◇ q15) ◇ q16) ◇ t) (apc2 q15 q15 q16)).symm).trans ((((cg (fun t => t ◇ ((q16 ◇ (q15 ◇ q15)) ◇ (q16 ◇ (q15 ◇ q15)))) (apc2 q15 q15 q16)).symm).trans (apc14 (q16 ◇ (q15 ◇ q15)))).trans (apc2 q15 q15 q16))
  have apc22 : forall (q17 q18:G), ((q18 ◇ q18) ◇ (q17 ◇ q17)) = ((q17 ◇ q17) ◇ (q18 ◇ q18)):=by
    intro q17 q18
    exact (((apc21 q17 (q18 ◇ q18)).symm).trans (apc2 q18 q18 (q17 ◇ q17))).symm
  have apc23 : forall (q19 q20 q21:G), ((q21 ◇ q21) ◇ ((q19 ◇ q19) ◇ q20)) = (((q19 ◇ q19) ◇ q20) ◇ (q21 ◇ q21)):=by
    intro q19 q20 q21
    exact ((((cg (fun t => t ◇ (q21 ◇ q21)) (apc2 q19 q19 q20)).symm).trans (apc22 q21 (q20 ◇ (q19 ◇ q19)))).trans (cg (fun t => (q21 ◇ q21) ◇ t) (apc2 q19 q19 q20))).symm
  have apc25 : forall (q22 q23:G), (((q23 ◇ q23) ◇ (q22 ◇ q23)) ◇ (q23 ◇ q23)) = ((q22 ◇ q23) ◇ (q23 ◇ q23)):=by
    intro q22 q23
    exact ((apc23 q23 (q22 ◇ q23) q23).symm).trans (((cg (fun t => t ◇ ((q23 ◇ q23) ◇ (q22 ◇ q23))) (apc16 q22 q23 q22)).symm).trans ((h (q22 ◇ q23) (q23 ◇ q23) q23).symm))
  have apc26 : forall (q24 q25:G), ((q25 ◇ q25) ◇ (q24 ◇ q25)) = ((q24 ◇ q25) ◇ (q25 ◇ q25)):=by
    intro q24 q25
    exact ((((cg (fun t => t ◇ ((q24 ◇ q25) ◇ (q25 ◇ q25))) (cg (fun t => ((q25 ◇ q25) ◇ (q24 ◇ q25)) ◇ t) (apc14 q25))).trans (cg (fun t => t ◇ ((q24 ◇ q25) ◇ (q25 ◇ q25))) (apc25 q24 q25))).trans (apc2 q25 q25 (q24 ◇ q25))).symm).trans ((((cg (fun t => (((q25 ◇ q25) ◇ (q24 ◇ q25)) ◇ ((q25 ◇ q25) ◇ (q25 ◇ q25))) ◇ t) (apc25 q24 q25)).symm).trans (apc1 (q25 ◇ q25) ((q25 ◇ q25) ◇ (q24 ◇ q25)) q24)).trans ((apc23 q25 (q24 ◇ q25) q25).trans (apc25 q24 q25)))
  have apc31 : forall (q26 q27:G), (((q26 ◇ q26) ◇ (q27 ◇ q26)) ◇ (q26 ◇ q26)) = (q26 ◇ q26):=by
    intro q26 q27
    exact (((cg (fun t => ((q26 ◇ q26) ◇ (q27 ◇ q26)) ◇ t) (apc20 q26)).symm).trans ((h q26 (q26 ◇ q26) q27).symm)).trans (apc19 q26)
  have apc32 : forall (q28 q29:G), (((q29 ◇ q28) ◇ (q28 ◇ q28)) ◇ (q28 ◇ q28)) = (q28 ◇ q28):=by
    intro q28 q29
    exact ((cg (fun t => ((q29 ◇ q28) ◇ (q28 ◇ q28)) ◇ t) (apc20 q28)).symm).trans ((((cg (fun t => t ◇ ((q28 ◇ q28) ◇ q28)) (apc26 q29 q28)).symm).trans ((h q28 (q28 ◇ q28) q29).symm)).trans (apc19 q28))
  have apc37 : forall (q30 q31:G), ((q30 ◇ q30) ◇ ((q31 ◇ q30) ◇ (q30 ◇ q30))) = (q30 ◇ q30):=by
    intro q30 q31
    exact (((((cg (fun t => t ◇ (q30 ◇ q30)) (cg (fun t => ((q31 ◇ q30) ◇ (q30 ◇ q30)) ◇ t) (apc14 q30))).trans (cg (fun t => t ◇ (q30 ◇ q30)) (apc32 q30 q31))).trans (apc14 q30)).symm).trans (((cg (fun t => (((q31 ◇ q30) ◇ (q30 ◇ q30)) ◇ ((q30 ◇ q30) ◇ (q30 ◇ q30))) ◇ t) (apc32 q30 q31)).symm).trans (apc1 (q30 ◇ q30) ((q31 ◇ q30) ◇ (q30 ◇ q30)) q30))).symm
  have apc38 : forall (q32 q33:G), ((q32 ◇ q32) ◇ (q33 ◇ q32)) = (q32 ◇ q32):=by
    intro q32 q33
    exact (((((cg (fun t => (((q33 ◇ q32) ◇ (q32 ◇ q32)) ◇ ((q33 ◇ q32) ◇ (q32 ◇ q32))) ◇ t) (apc32 q32 q33)).trans (cg (fun t => t ◇ (q32 ◇ q32)) (apc2 q32 q32 (q33 ◇ q32)))).trans (apc31 q32 q33)).symm).trans ((((cg (fun t => (((q33 ◇ q32) ◇ (q32 ◇ q32)) ◇ ((q33 ◇ q32) ◇ (q32 ◇ q32))) ◇ t) (cg (fun t => ((q33 ◇ q32) ◇ (q32 ◇ q32)) ◇ t) (apc37 q32 q33))).symm).trans (apc16 (q32 ◇ q32) ((q33 ◇ q32) ◇ (q32 ◇ q32)) q32)).trans (apc2 q32 q32 (q33 ◇ q32)))).symm
  have apc39 : forall (q24 q25 q32 q33:G), ((q24 ◇ q25) ◇ (q25 ◇ q25)) = (q25 ◇ q25):=by
    intro q24 q25 q32 q33
    exact (((apc38 q25 q24).symm).trans (apc26 q24 q25)).symm
  have apc40 : forall (q34 q35:G), (q35 ◇ (q34 ◇ q35)) = (q35 ◇ q35):=by
    intro q34 q35
    exact (((apc38 q35 (q34 ◇ q35)).symm).trans (((cg (fun t => t ◇ ((q34 ◇ q35) ◇ q35)) (apc39 q34 q35 q34 q34)).symm).trans ((h q35 (q34 ◇ q35) q35).symm))).symm
  have apc41 : forall (q36 q37:G), ((q36 ◇ q37) ◇ (q36 ◇ q37)) = (q37 ◇ q37):=by
    intro q36 q37
    exact (((apc39 q36 q37 ((q36 ◇ q37) ◇ (q37 ◇ q37)) ((q36 ◇ q37) ◇ (q37 ◇ q37))).symm).trans (((cg (fun t => (q36 ◇ q37) ◇ t) (apc40 q36 q37)).symm).trans (apc40 q37 (q36 ◇ q37)))).symm
  have apc42 : forall (q38 q39:G), (q39 ◇ q39) = (q38 ◇ q38):=by
    intro q38 q39
    exact (((cg (fun t => (q38 ◇ q39) ◇ t) (apc1 q38 q39 ((q39 ◇ (q38 ◇ q38)) ◇ (q39 ◇ q38)))).trans (apc41 q38 q39)).symm).trans ((((cg (fun t => t ◇ ((q39 ◇ (q38 ◇ q38)) ◇ (q39 ◇ q38))) (apc1 q38 q39 q38)).symm).trans (apc41 (q39 ◇ (q38 ◇ q38)) (q39 ◇ q38))).trans (apc41 q39 q38))
  have apc43 : forall (q15 q16 q36 q37:G), ((q15 ◇ q15) ◇ q16) = (q16 ◇ q16):=by
    intro q15 q16 q36 q37
    exact (((apc41 (q15 ◇ q15) q16).symm).trans (apc21 q15 q16)).symm
  have apc44 : forall (q40 q41:G), (q41 ◇ (q40 ◇ q40)) = (q41 ◇ q41):=by
    intro q40 q41
    exact ((cg (fun t => q41 ◇ t) (apc42 q40 q41)).symm).trans (apc40 q41 q41)
  have apc45 : forall (q42 q43:G), (q42 ◇ q43) = (q42 ◇ q42):=by
    intro q42 q43
    exact ((((apc43 q43 (q43 ◇ q42) ((q43 ◇ q43) ◇ (q43 ◇ q42)) ((q43 ◇ q43) ◇ (q43 ◇ q42))).trans (apc41 q43 q42)).symm).trans (((cg (fun t => t ◇ (q43 ◇ q42)) (apc44 q42 q43)).symm).trans ((h q42 q43 q42).symm))).symm
  have apc57 : forall (q44 q45:G), ((q45 ◇ q45) ◇ (q45 ◇ q45)) = ((q45 ◇ q44) ◇ q45):=by
    intro q44 q45
    exact ((cg (fun t => (q45 ◇ q45) ◇ t) (apc45 q45 (q45 ◇ q44))).symm).trans (((cg (fun t => t ◇ (q45 ◇ (q45 ◇ q44))) (apc40 q44 q45)).symm).trans (apc2 q44 q45 q45))
  have apc58 : forall (q44 q45:G), ((q45 ◇ q44) ◇ q45) = (q45 ◇ q45):=by
    intro q44 q45
    exact (((apc57 q44 q45).symm).trans (apc57 q45 q45)).trans (apc43 q45 q45 ((q45 ◇ q45) ◇ q45) ((q45 ◇ q45) ◇ q45))
  have apc59 : forall (q46 q47:G), ((q47 ◇ q46) ◇ (q47 ◇ q46)) = (q47 ◇ q47):=by
    intro q46 q47
    exact (((apc58 q46 q47).symm).trans (apc45 (q47 ◇ q46) q47)).symm
  have apc60 : forall (q48 q49 q50:G), ((q49 ◇ q48) ◇ q50) = (q50 ◇ q50):=by
    intro q48 q49 q50
    exact (((((cg (fun t => (q50 ◇ (q49 ◇ q49)) ◇ t) (apc45 q50 (q49 ◇ q48))).trans (cg (fun t => t ◇ (q50 ◇ q50)) (apc45 q50 (q49 ◇ q49)))).trans (apc59 q50 q50)).symm).trans (((cg (fun t => t ◇ (q50 ◇ (q49 ◇ q48))) (cg (fun t => q50 ◇ t) (apc59 q48 q49))).symm).trans ((h (q49 ◇ q48) q50 (q49 ◇ q48)).symm))).symm
  exact (calc
    (x ◇ x) = (y ◇ y):=apc42 y x
    _ = (((x ◇ y) ◇ (x ◇ z)) ◇ y):=(apc60 (x ◇ z) (x ◇ y) y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48100_to_51198 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48100_to_51198
