-- Equation50698 → Equation42404
-- Recorded verdict: true
-- Premise: x * y = (y * ((y * x) * z)) * z
-- Conclusion: x * y = z * (w * (u * (v * v)))
-- Original submission SHA-256: 94af36d12b7a8725be994958c8dbc7d3ee145cab3057134c268dd6451562ebc5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ ((y ◇ x) ◇ z)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = z ◇ (w ◇ (u ◇ (v ◇ v)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (((q1 ◇ q0) ◇ q2) ◇ q1) = ((q1 ◇ (q0 ◇ q1)) ◇ q2):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ q2) (cg (fun t => q1 ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h ((q1 ◇ q0) ◇ q2) q1 q2).symm)).symm
  have apc1 : forall (x y z:G), ((y ◇ ((y ◇ x) ◇ z)) ◇ z) = ((y ◇ ((y ◇ x) ◇ x)) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc2 : forall (x y z:G), ((y ◇ ((y ◇ x) ◇ x)) ◇ x) = (x ◇ y):=by
    intro x y z
    exact ((h x y x).trans (apc1 x y x)).symm
  have apc3 : forall (q3 q4:G), (((q3 ◇ q4) ◇ q4) ◇ q3) = ((q3 ◇ (q4 ◇ q3)) ◇ q4):=by
    intro q3 q4
    exact (((cg (fun t => t ◇ q4) (cg (fun t => q3 ◇ t) (apc2 q4 q3 q3))).symm).trans ((h ((q3 ◇ q4) ◇ q4) q3 q4).symm)).symm
  have apc4 : forall (q5 q6 q7:G), ((q6 ◇ (((q6 ◇ q5) ◇ q7) ◇ q6)) ◇ q7) = ((q5 ◇ q6) ◇ q6):=by
    intro q5 q6 q7
    exact (((cg (fun t => t ◇ q6) ((h q5 q6 q7).symm)).symm).trans (apc0 ((q6 ◇ q5) ◇ q7) q6 q7)).symm
  have apc5 : forall (q8 q9 q10:G), ((((q9 ◇ q8) ◇ q10) ◇ q9) ◇ q9) = ((q9 ◇ ((q8 ◇ q9) ◇ q9)) ◇ q10):=by
    intro q8 q9 q10
    exact (((cg (fun t => t ◇ q10) (cg (fun t => q9 ◇ t) (apc4 q8 q9 q10))).symm).trans ((h (((q9 ◇ q8) ◇ q10) ◇ q9) q9 q10).symm)).symm
  have apc6 : forall (q11 q12:G), ((((q11 ◇ q12) ◇ q12) ◇ q11) ◇ q11) = ((q11 ◇ ((q12 ◇ q11) ◇ q11)) ◇ q12):=by
    intro q11 q12
    exact (((cg (fun t => t ◇ q12) (cg (fun t => q11 ◇ t) (cg (fun t => t ◇ q11) (apc2 q12 q11 q11)))).symm).trans (apc4 ((q11 ◇ q12) ◇ q12) q11 q12)).symm
  have apc8 : forall (q13 q14:G), (((q13 ◇ (q14 ◇ q13)) ◇ q14) ◇ q13) = ((q13 ◇ ((q14 ◇ q13) ◇ q13)) ◇ q14):=by
    intro q13 q14
    exact ((cg (fun t => t ◇ q13) (apc3 q13 q14)).symm).trans (apc5 q14 q13 q14)
  have apc9 : forall (q15 q16 q17:G), ((q16 ◇ ((q16 ◇ (q15 ◇ q16)) ◇ q17)) ◇ q17) = ((q15 ◇ q16) ◇ q16):=by
    intro q15 q16 q17
    exact ((cg (fun t => t ◇ q17) (cg (fun t => q16 ◇ t) (apc0 q15 q16 q17))).symm).trans (apc4 q15 q16 q17)
  have apc10 : forall (q18 q19:G), (((q19 ◇ q18) ◇ q19) ◇ q19) = ((q19 ◇ (q18 ◇ q19)) ◇ q19):=by
    intro q18 q19
    exact (((cg (fun t => t ◇ q19) (cg (fun t => q19 ◇ t) ((h q18 q19 q19).symm))).symm).trans (apc9 (q19 ◇ q18) q19 q19)).symm
  have apc11 : forall (q20:G), (((q20 ◇ q20) ◇ q20) ◇ q20) = ((q20 ◇ (q20 ◇ q20)) ◇ q20):=by
    intro q20
    exact (((cg (fun t => t ◇ q20) (cg (fun t => q20 ◇ t) (apc2 q20 q20 q20))).symm).trans (apc9 (q20 ◇ q20) q20 q20)).symm
  have apc12 : forall (q21:G), (((q21 ◇ (q21 ◇ q21)) ◇ q21) ◇ q21) = (q21 ◇ q21):=by
    intro q21
    exact (((cg (fun t => t ◇ q21) (apc10 q21 q21)).symm).trans (apc6 q21 q21)).trans (apc2 q21 q21 ((q21 ◇ ((q21 ◇ q21) ◇ q21)) ◇ q21))
  have apc16 : forall (q22:G), ((((q22 ◇ q22) ◇ q22) ◇ q22) ◇ q22) = (q22 ◇ q22):=by
    intro q22
    exact ((((apc9 (q22 ◇ (q22 ◇ q22)) q22 q22).trans (apc12 q22)).symm).trans (((cg (fun t => t ◇ q22) (cg (fun t => q22 ◇ t) (cg (fun t => t ◇ q22) (cg (fun t => q22 ◇ t) (apc11 q22))))).symm).trans (apc9 ((q22 ◇ q22) ◇ q22) q22 q22))).symm
  have apc18 : forall (q23 q24 q20:G), ((q24 ◇ ((q24 ◇ (q24 ◇ q23)) ◇ q20)) ◇ q20) = ((q24 ◇ q23) ◇ q24):=by
    intro q23 q24 q20
    exact (((cg (fun t => t ◇ q20) (cg (fun t => q24 ◇ t) (cg (fun t => t ◇ q20) (cg (fun t => q24 ◇ t) (apc2 q24 q23 q23))))).symm).trans (apc9 (q23 ◇ ((q23 ◇ q24) ◇ q24)) q24 q20)).trans (cg (fun t => t ◇ q24) (apc2 q24 q23 ((q23 ◇ ((q23 ◇ q24) ◇ q24)) ◇ q24)))
  have apc21 : forall (q25 q26 q27:G), ((q27 ◇ (q25 ◇ q27)) ◇ (((q27 ◇ q25) ◇ q26) ◇ q27)) = (q26 ◇ (q27 ◇ q25)):=by
    intro q25 q26 q27
    exact ((apc0 q25 q27 (((q27 ◇ q25) ◇ q26) ◇ q27)).symm).trans ((h q26 (q27 ◇ q25) q27).symm)
  have apc22 : forall (q25 q26 q27:G), ((q27 ◇ (q25 ◇ q27)) ◇ ((q27 ◇ (q25 ◇ q27)) ◇ q26)) = (q26 ◇ (q27 ◇ q25)):=by
    intro q25 q26 q27
    exact ((apc0 q25 q27 ((q27 ◇ (q25 ◇ q27)) ◇ q26)).symm).trans (((cg (fun t => t ◇ q27) (cg (fun t => (q27 ◇ q25) ◇ t) (apc0 q25 q27 q26))).symm).trans ((h q26 (q27 ◇ q25) q27).symm))
  have apc23 : forall (q28 q29:G), ((q29 ◇ ((q29 ◇ q28) ◇ q29)) ◇ (q28 ◇ q29)) = (q29 ◇ (q29 ◇ (q29 ◇ q28))):=by
    intro q28 q29
    exact ((cg (fun t => (q29 ◇ ((q29 ◇ q28) ◇ q29)) ◇ t) ((h q28 q29 q29).symm)).symm).trans (apc22 (q29 ◇ q28) q29 q29)
  have apc24 : forall (q30 q31:G), (q31 ◇ (q31 ◇ (q31 ◇ ((q31 ◇ q30) ◇ q31)))) = (q31 ◇ (q31 ◇ q30)):=by
    intro q30 q31
    exact (((apc21 q30 q31 q31).symm).trans (((cg (fun t => t ◇ (((q31 ◇ q30) ◇ q31) ◇ q31)) (cg (fun t => q31 ◇ t) ((h q30 q31 q31).symm))).symm).trans (apc23 ((q31 ◇ q30) ◇ q31) q31))).symm
  have apc25 : forall (q32 q33:G), (q33 ◇ (q33 ◇ ((q33 ◇ q32) ◇ q33))) = (q33 ◇ (q33 ◇ (q33 ◇ (q32 ◇ q33)))):=by
    intro q32 q33
    exact (((cg (fun t => q33 ◇ t) (cg (fun t => q33 ◇ t) (cg (fun t => q33 ◇ t) ((h q32 q33 q33).symm)))).symm).trans (apc24 ((q33 ◇ q32) ◇ q33) q33)).symm
  have apc28 : forall (q34 q35:G), ((q35 ◇ ((q35 ◇ q34) ◇ q35)) ◇ q35) = ((q35 ◇ (q35 ◇ (q34 ◇ q35))) ◇ q35):=by
    intro q34 q35
    exact (((apc18 (q35 ◇ (q34 ◇ q35)) q35 q34).symm).trans (((cg (fun t => t ◇ q34) (cg (fun t => q35 ◇ t) (cg (fun t => t ◇ q34) (apc25 q34 q35)))).symm).trans ((h (q35 ◇ ((q35 ◇ q34) ◇ q35)) q35 q34).symm))).symm
  have apc29 : forall (q36 q37:G), ((q37 ◇ (q37 ◇ (q36 ◇ q37))) ◇ q37) = (q36 ◇ q37):=by
    intro q36 q37
    exact ((apc28 q36 q37).symm).trans ((h q36 q37 q37).symm)
  have apc31 : forall (q38 q39:G), ((q39 ◇ (q39 ◇ (q39 ◇ q38))) ◇ q39) = (q39 ◇ q38):=by
    intro q38 q39
    exact (((cg (fun t => t ◇ q39) (cg (fun t => q39 ◇ t) (cg (fun t => q39 ◇ t) (apc2 q39 q38 q38)))).symm).trans (apc29 (q38 ◇ ((q38 ◇ q39) ◇ q39)) q39)).trans (apc2 q39 q38 ((q38 ◇ ((q38 ◇ q39) ◇ q39)) ◇ q39))
  have apc40 : forall (q40 q41 q42:G), (((((q41 ◇ q40) ◇ q42) ◇ q41) ◇ q41) ◇ q41) = ((q41 ◇ (((q40 ◇ q41) ◇ q41) ◇ q41)) ◇ q42):=by
    intro q40 q41 q42
    exact (((cg (fun t => t ◇ q42) (cg (fun t => q41 ◇ t) (cg (fun t => t ◇ q41) (apc4 q40 q41 q42)))).symm).trans (apc4 (((q41 ◇ q40) ◇ q42) ◇ q41) q41 q42)).symm
  have apc41 : forall (q43:G), (((q43 ◇ (q43 ◇ q43)) ◇ (q43 ◇ q43)) ◇ q43) = (q43 ◇ (q43 ◇ (q43 ◇ q43))):=by
    intro q43
    exact ((cg (fun t => t ◇ q43) (cg (fun t => (q43 ◇ (q43 ◇ q43)) ◇ t) (apc2 q43 q43 ((q43 ◇ ((q43 ◇ q43) ◇ q43)) ◇ q43)))).symm).trans (((cg (fun t => t ◇ q43) (cg (fun t => (q43 ◇ (q43 ◇ q43)) ◇ t) (apc8 q43 q43))).symm).trans (apc2 q43 (q43 ◇ (q43 ◇ q43)) q43))
  have apc42 : forall (q44:G), ((q44 ◇ (q44 ◇ q44)) ◇ (q44 ◇ q44)) = ((q44 ◇ q44) ◇ q44):=by
    intro q44
    exact (((cg (fun t => t ◇ q44) (apc29 q44 q44)).symm).trans ((((cg (fun t => t ◇ q44) (cg (fun t => t ◇ q44) (apc41 q44))).symm).trans (apc40 (q44 ◇ q44) q44 (q44 ◇ q44))).trans (cg (fun t => t ◇ (q44 ◇ q44)) (cg (fun t => q44 ◇ t) (apc16 q44))))).symm
  have apc43 : forall (q45:G), ((q45 ◇ q45) ◇ q45) = (q45 ◇ (q45 ◇ (q45 ◇ q45))):=by
    intro q45
    exact (((apc23 q45 q45).symm).trans (((cg (fun t => t ◇ (q45 ◇ q45)) (cg (fun t => q45 ◇ t) (apc42 q45))).symm).trans ((h (q45 ◇ q45) q45 (q45 ◇ q45)).symm))).symm
  have apc44 : forall (q46:G), (q46 ◇ (q46 ◇ q46)) = (q46 ◇ q46):=by
    intro q46
    exact ((apc31 (q46 ◇ q46) q46).symm).trans (((cg (fun t => t ◇ q46) (cg (fun t => q46 ◇ t) (apc43 q46))).symm).trans ((h q46 q46 q46).symm))
  have apc45 : forall (q47:G), (((q47 ◇ q47) ◇ q47) ◇ q47) = (q47 ◇ q47):=by
    intro q47
    exact (((cg (fun t => t ◇ q47) (cg (fun t => t ◇ q47) (cg (fun t => q47 ◇ t) (apc44 q47)))).trans (cg (fun t => t ◇ q47) (cg (fun t => t ◇ q47) (apc44 q47)))).symm).trans (((cg (fun t => t ◇ q47) (cg (fun t => t ◇ q47) (apc43 q47))).symm).trans (apc16 q47))
  have apc46 : forall (q22 q47:G), ((q22 ◇ q22) ◇ q22) = (q22 ◇ q22):=by
    intro q22 q47
    exact ((cg (fun t => t ◇ q22) (apc45 q22)).symm).trans (apc16 q22)
  have apc47 : forall (q48 q49:G), ((q48 ◇ ((q48 ◇ q48) ◇ q49)) ◇ q49) = (q48 ◇ q48):=by
    intro q48 q49
    exact ((((cg (fun t => t ◇ q49) (cg (fun t => q48 ◇ t) (cg (fun t => t ◇ q49) (cg (fun t => q48 ◇ t) (cg (fun t => q48 ◇ t) (apc44 q48)))))).trans (cg (fun t => t ◇ q49) (cg (fun t => q48 ◇ t) (cg (fun t => t ◇ q49) (cg (fun t => q48 ◇ t) (apc44 q48)))))).trans (cg (fun t => t ◇ q49) (cg (fun t => q48 ◇ t) (cg (fun t => t ◇ q49) (apc44 q48))))).symm).trans ((((cg (fun t => t ◇ q49) (cg (fun t => q48 ◇ t) (cg (fun t => t ◇ q49) (cg (fun t => q48 ◇ t) (apc43 q48))))).symm).trans (apc9 (q48 ◇ q48) q48 q49)).trans ((cg (fun t => t ◇ q48) (apc46 q48 ((q48 ◇ q48) ◇ q48))).trans (apc46 q48 ((q48 ◇ q48) ◇ q48))))
  have apc48 : forall (q50:G), ((q50 ◇ q50) ◇ (q50 ◇ q50)) = (q50 ◇ q50):=by
    intro q50
    exact (((((cg (fun t => t ◇ (q50 ◇ q50)) (cg (fun t => q50 ◇ t) (cg (fun t => t ◇ q50) (cg (fun t => q50 ◇ t) (apc46 q50 ((q50 ◇ q50) ◇ q50)))))).trans (cg (fun t => t ◇ (q50 ◇ q50)) (cg (fun t => q50 ◇ t) (cg (fun t => t ◇ q50) (apc44 q50))))).trans (cg (fun t => t ◇ (q50 ◇ q50)) (cg (fun t => q50 ◇ t) (apc46 q50 ((q50 ◇ q50) ◇ q50))))).trans (cg (fun t => t ◇ (q50 ◇ q50)) (apc44 q50))).symm).trans ((((cg (fun t => (q50 ◇ ((q50 ◇ ((q50 ◇ q50) ◇ q50)) ◇ q50)) ◇ t) (apc45 q50)).symm).trans (apc23 ((q50 ◇ q50) ◇ q50) q50)).trans ((((cg (fun t => q50 ◇ t) (cg (fun t => q50 ◇ t) (cg (fun t => q50 ◇ t) (apc46 q50 ((q50 ◇ q50) ◇ q50))))).trans (cg (fun t => q50 ◇ t) (cg (fun t => q50 ◇ t) (apc44 q50)))).trans (cg (fun t => q50 ◇ t) (apc44 q50))).trans (apc44 q50)))
  have apc51 : forall (q51 q52:G), ((q52 ◇ (q52 ◇ (q51 ◇ q51))) ◇ q52) = (q51 ◇ q51):=by
    intro q51 q52
    exact (((cg (fun t => t ◇ q52) (cg (fun t => q52 ◇ t) (cg (fun t => q52 ◇ t) (apc47 q51 q52)))).symm).trans (apc29 (q51 ◇ ((q51 ◇ q51) ◇ q52)) q52)).trans (apc47 q51 q52)
  have apc52 : forall (q53 q54:G), ((q53 ◇ q53) ◇ ((q53 ◇ q53) ◇ q54)) = (q54 ◇ (q53 ◇ q53)):=by
    intro q53 q54
    exact ((cg (fun t => (q53 ◇ q53) ◇ t) (cg (fun t => t ◇ q54) (apc44 q53))).symm).trans (((cg (fun t => t ◇ ((q53 ◇ (q53 ◇ q53)) ◇ q54)) (apc44 q53)).symm).trans (apc22 q53 q54 q53))
  have apc53 : forall (q55 q56:G), ((q56 ◇ (q55 ◇ q55)) ◇ q56) = (q55 ◇ q55):=by
    intro q55 q56
    exact (((cg (fun t => t ◇ q56) (cg (fun t => (q55 ◇ q55) ◇ t) (cg (fun t => t ◇ q56) (apc48 q55)))).trans (cg (fun t => t ◇ q56) (apc52 q55 q56))).symm).trans ((((cg (fun t => t ◇ q56) (cg (fun t => (q55 ◇ q55) ◇ t) (cg (fun t => t ◇ q56) (apc52 q55 (q55 ◇ q55))))).symm).trans (apc9 (q55 ◇ q55) (q55 ◇ q55) q56)).trans ((cg (fun t => t ◇ (q55 ◇ q55)) (apc48 q55)).trans (apc48 q55)))
  have apc54 : forall (q57 q58:G), (q58 ◇ q58) = (q57 ◇ q57):=by
    intro q57 q58
    exact (((apc53 q57 ((q58 ◇ q58) ◇ (q57 ◇ q57))).symm).trans (((cg (fun t => t ◇ ((q58 ◇ q58) ◇ (q57 ◇ q57))) (cg (fun t => ((q58 ◇ q58) ◇ (q57 ◇ q57)) ◇ t) (apc53 q57 (q58 ◇ q58)))).symm).trans (apc51 q58 ((q58 ◇ q58) ◇ (q57 ◇ q57))))).symm
  have apc55 : forall (q59 q60:G), ((q59 ◇ q59) ◇ q60) = (q59 ◇ q59):=by
    intro q59 q60
    exact (((apc53 q59 q60).symm).trans (((cg (fun t => t ◇ q60) (cg (fun t => q60 ◇ t) (apc53 q59 q60))).symm).trans ((h (q59 ◇ q59) q60 q60).symm))).symm
  have apc56 : forall (q61 q62:G), (q62 ◇ (q61 ◇ q61)) = (q62 ◇ q62):=by
    intro q61 q62
    exact ((cg (fun t => q62 ◇ t) (apc54 q61 q62)).symm).trans (apc44 q62)
  have apc57 : forall (q63 q64:G), (q64 ◇ q64) = (q63 ◇ q64):=by
    intro q63 q64
    exact ((apc55 q64 (q64 ◇ q63)).symm).trans (((cg (fun t => t ◇ (q64 ◇ q63)) (apc56 (q64 ◇ q63) q64)).symm).trans ((h q63 q64 (q64 ◇ q63)).symm))
  have apc58 : forall (q65 q66 q67:G), (q67 ◇ q67) = (q65 ◇ q66):=by
    intro q65 q66 q67
    exact (apc57 (q66 ◇ ((q66 ◇ q65) ◇ q67)) q67).trans ((h q65 q66 q67).symm)
  exact ((apc58 x y (x ◇ y)).symm).trans (apc58 z (w ◇ (u ◇ (v ◇ v))) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50698_to_42404 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_50698_to_42404
