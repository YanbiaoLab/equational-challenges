-- Equation26286 → Equation20934
-- Recorded verdict: true
-- Premise: x = (y * ((z * x) * z)) * (y * x)
-- Conclusion: x = (y * y) * (((z * y) * z) * x)
-- Original submission SHA-256: 12dfb65591364718711c4ceeb96d5b40dcbb11951f7f526b634c1c3543838e57
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ ((z ◇ x) ◇ z)) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ (((z ◇ y) ◇ z) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ (((q2 ◇ q1) ◇ ((q0 ◇ q2) ◇ q0)) ◇ q1)) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (((q2 ◇ q1) ◇ ((q0 ◇ q2) ◇ q0)) ◇ q1)) ((h q2 (q2 ◇ q1) q0).symm)).symm).trans ((h q1 ((q2 ◇ q1) ◇ ((q0 ◇ q2) ◇ q0)) q2).symm)
  have apc1 : forall (x y z:G), ((y ◇ ((z ◇ x) ◇ z)) ◇ (y ◇ x)) = ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc2 : forall (x y z:G), ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) = x:=by
    intro x y z
    exact ((h x x x).trans (apc1 x x x)).symm
  have apc3 : forall (q3 q4 q0 q2:G), (((q4 ◇ ((q0 ◇ q3) ◇ q0)) ◇ ((q2 ◇ (q4 ◇ q3)) ◇ q2)) ◇ q3) = (q4 ◇ q3):=by
    intro q3 q4 q0 q2
    exact ((cg (fun t => ((q4 ◇ ((q0 ◇ q3) ◇ q0)) ◇ ((q2 ◇ (q4 ◇ q3)) ◇ q2)) ◇ t) ((h q3 q4 q0).symm)).symm).trans ((h (q4 ◇ q3) (q4 ◇ ((q0 ◇ q3) ◇ q0)) q2).symm)
  have apc4 : forall (q3 q4 q0 q5:G), ((q5 ◇ (q3 ◇ (q4 ◇ ((q0 ◇ q3) ◇ q0)))) ◇ (q5 ◇ (q4 ◇ q3))) = (q4 ◇ q3):=by
    intro q3 q4 q0 q5
    exact ((cg (fun t => t ◇ (q5 ◇ (q4 ◇ q3))) (cg (fun t => q5 ◇ t) (cg (fun t => t ◇ (q4 ◇ ((q0 ◇ q3) ◇ q0))) ((h q3 q4 q0).symm)))).symm).trans ((h (q4 ◇ q3) q5 (q4 ◇ ((q0 ◇ q3) ◇ q0))).symm)
  have apc5 : forall (q6 q7 q8 q9:G), (((q8 ◇ ((q9 ◇ q7) ◇ q9)) ◇ (q7 ◇ (q8 ◇ ((q6 ◇ q7) ◇ q6)))) ◇ q7) = (q8 ◇ q7):=by
    intro q6 q7 q8 q9
    exact ((cg (fun t => t ◇ q7) (cg (fun t => (q8 ◇ ((q9 ◇ q7) ◇ q9)) ◇ t) (cg (fun t => t ◇ (q8 ◇ ((q6 ◇ q7) ◇ q6))) ((h q7 q8 q6).symm)))).symm).trans (apc3 q7 q8 q9 (q8 ◇ ((q6 ◇ q7) ◇ q6)))
  have apc7 : forall (q10 q11 q12 q13:G), ((q12 ◇ (q11 ◇ q13)) ◇ (q12 ◇ (((q13 ◇ q11) ◇ ((q10 ◇ q13) ◇ q10)) ◇ q11))) = (((q13 ◇ q11) ◇ ((q10 ◇ q13) ◇ q10)) ◇ q11):=by
    intro q10 q11 q12 q13
    exact ((cg (fun t => t ◇ (q12 ◇ (((q13 ◇ q11) ◇ ((q10 ◇ q13) ◇ q10)) ◇ q11))) (cg (fun t => q12 ◇ t) (cg (fun t => t ◇ q13) (apc0 q10 q11 q13)))).symm).trans ((h (((q13 ◇ q11) ◇ ((q10 ◇ q13) ◇ q10)) ◇ q11) q12 q13).symm)
  have apc8 : forall (q14 q15 q16:G), (((q16 ◇ q15) ◇ ((q14 ◇ q16) ◇ q14)) ◇ q15) = ((q16 ◇ (q15 ◇ q16)) ◇ q15):=by
    intro q14 q15 q16
    exact (((cg (fun t => (q16 ◇ (q15 ◇ q16)) ◇ t) (apc0 q14 q15 q16)).symm).trans (apc7 q14 q15 q16 q16)).symm
  have apc9 : forall (q0 q1 q2 q14 q15 q16:G), (q2 ◇ ((q2 ◇ (q1 ◇ q2)) ◇ q1)) = q1:=by
    intro q0 q1 q2 q14 q15 q16
    exact ((cg (fun t => q2 ◇ t) (apc8 q1 q1 q2)).symm).trans (apc0 q1 q1 q2)
  have apc10 : forall (q17:G), (q17 ◇ (q17 ◇ (q17 ◇ q17))) = (q17 ◇ q17):=by
    intro q17
    exact ((cg (fun t => t ◇ (q17 ◇ (q17 ◇ q17))) (apc9 q17 q17 q17 q17 q17 q17)).symm).trans ((h (q17 ◇ q17) q17 q17).symm)
  have apc11 : forall (q10 q11 q12 q13 q14 q15 q16:G), ((q12 ◇ (q11 ◇ q13)) ◇ (q12 ◇ ((q13 ◇ (q11 ◇ q13)) ◇ q11))) = ((q13 ◇ (q11 ◇ q13)) ◇ q11):=by
    intro q10 q11 q12 q13 q14 q15 q16
    exact ((cg (fun t => (q12 ◇ (q11 ◇ q13)) ◇ t) (cg (fun t => q12 ◇ t) (apc8 q11 q11 q13))).symm).trans ((apc7 q11 q11 q12 q13).trans (apc8 q11 q11 q13))
  have apc12 : forall (q18 q19:G), ((q18 ◇ ((q19 ◇ q19) ◇ q19)) ◇ (q18 ◇ q19)) = q19:=by
    intro q18 q19
    exact (((cg (fun t => (q18 ◇ ((q19 ◇ q19) ◇ q19)) ◇ t) (cg (fun t => q18 ◇ t) (apc2 q19 q18 q18))).symm).trans (apc11 q18 (q19 ◇ q19) q18 q19 q18 q18 q18)).trans (apc2 q19 ((q19 ◇ ((q19 ◇ q19) ◇ q19)) ◇ (q19 ◇ q19)) ((q19 ◇ ((q19 ◇ q19) ◇ q19)) ◇ (q19 ◇ q19)))
  have apc13 : forall (q20 q21 q22:G), ((q22 ◇ ((q22 ◇ q20) ◇ q22)) ◇ (q22 ◇ q20)) = ((q21 ◇ ((q22 ◇ q20) ◇ q22)) ◇ (q21 ◇ q20)):=by
    intro q20 q21 q22
    exact (((cg (fun t => (q21 ◇ ((q22 ◇ q20) ◇ q22)) ◇ t) (cg (fun t => q21 ◇ t) ((h q20 q22 q22).symm))).symm).trans (apc11 q20 (q22 ◇ q20) q21 q22 q20 q20 q20)).symm
  have apc14 : forall (q23 q24:G), ((q24 ◇ ((q24 ◇ q23) ◇ q24)) ◇ (q24 ◇ q23)) = q23:=by
    intro q23 q24
    exact (apc13 q23 q23 q24).trans ((h q23 q23 q24).symm)
  have apc15 : forall (q25:G), (q25 ◇ (q25 ◇ q25)) = q25:=by
    intro q25
    exact ((((cg (fun t => (q25 ◇ ((q25 ◇ q25) ◇ q25)) ◇ t) (apc10 q25)).trans (apc12 q25 q25)).symm).trans (((cg (fun t => t ◇ (q25 ◇ (q25 ◇ (q25 ◇ q25)))) (cg (fun t => q25 ◇ t) (cg (fun t => t ◇ q25) (apc10 q25)))).symm).trans (apc14 (q25 ◇ (q25 ◇ q25)) q25))).symm
  have apc16 : forall (q26:G), ((q26 ◇ q26) ◇ (((q26 ◇ q26) ◇ q26) ◇ q26)) = q26:=by
    intro q26
    exact ((cg (fun t => (q26 ◇ q26) ◇ t) (cg (fun t => t ◇ q26) (cg (fun t => (q26 ◇ q26) ◇ t) (apc15 q26)))).symm).trans (apc9 q26 q26 (q26 ◇ q26) q26 q26 q26)
  have apc17 : forall (q27 q28:G), ((q28 ◇ ((q27 ◇ q28) ◇ q27)) ◇ (q28 ◇ q28)) = q28:=by
    intro q27 q28
    exact (((cg (fun t => t ◇ (q28 ◇ q28)) (cg (fun t => t ◇ ((q27 ◇ q28) ◇ q27)) (apc15 q28))).symm).trans (apc8 q27 (q28 ◇ q28) q28)).trans (apc12 q28 q28)
  have apc18 : forall (q29 q30:G), ((q29 ◇ (q30 ◇ q30)) ◇ (q29 ◇ (q30 ◇ q30))) = (q30 ◇ q30):=by
    intro q29 q30
    exact ((cg (fun t => t ◇ (q29 ◇ (q30 ◇ q30))) (cg (fun t => q29 ◇ t) (cg (fun t => t ◇ q30) (apc15 q30)))).symm).trans ((h (q30 ◇ q30) q29 q30).symm)
  have apc19 : forall (q31 q32:G), ((q31 ◇ (q32 ◇ q32)) ◇ (q32 ◇ q32)) = (q31 ◇ (q32 ◇ q32)):=by
    intro q31 q32
    exact ((cg (fun t => (q31 ◇ (q32 ◇ q32)) ◇ t) (apc18 q31 q32)).symm).trans (apc15 (q31 ◇ (q32 ◇ q32)))
  have apc20 : forall (q29 q30:G), ((q29 ◇ ((q30 ◇ (q29 ◇ q29)) ◇ q30)) ◇ q29) = (q29 ◇ q29):=by
    intro q29 q30
    exact ((cg (fun t => (q29 ◇ ((q30 ◇ (q29 ◇ q29)) ◇ q30)) ◇ t) (apc15 q29)).symm).trans ((h (q29 ◇ q29) q29 q30).symm)
  have apc24 : forall (q33 q34:G), (q34 ◇ (q34 ◇ ((q33 ◇ (q34 ◇ q34)) ◇ q33))) = ((q33 ◇ (q34 ◇ q34)) ◇ q33):=by
    intro q33 q34
    exact ((cg (fun t => t ◇ (q34 ◇ ((q33 ◇ (q34 ◇ q34)) ◇ q33))) (apc15 q34)).symm).trans (((cg (fun t => t ◇ (q34 ◇ ((q33 ◇ (q34 ◇ q34)) ◇ q33))) (cg (fun t => q34 ◇ t) (apc20 q34 q33))).symm).trans (apc14 ((q33 ◇ (q34 ◇ q34)) ◇ q33) q34))
  have apc25 : forall (q35 q36:G), ((q35 ◇ (q35 ◇ (q35 ◇ ((q36 ◇ q35) ◇ q36)))) ◇ q35) = (q35 ◇ q35):=by
    intro q35 q36
    exact ((cg (fun t => (q35 ◇ (q35 ◇ (q35 ◇ ((q36 ◇ q35) ◇ q36)))) ◇ t) (apc15 q35)).symm).trans (apc4 q35 q35 q36 q35)
  have apc39 : forall (q37 q38:G), (q38 ◇ (q38 ◇ (q38 ◇ (q38 ◇ ((q37 ◇ q38) ◇ q37))))) = (q38 ◇ (q38 ◇ ((q37 ◇ q38) ◇ q37))):=by
    intro q37 q38
    exact (((cg (fun t => q38 ◇ t) (cg (fun t => q38 ◇ t) (cg (fun t => t ◇ (q38 ◇ ((q37 ◇ q38) ◇ q37))) ((h q38 q38 q37).symm)))).symm).trans (apc24 (q38 ◇ ((q37 ◇ q38) ◇ q37)) q38)).trans (cg (fun t => t ◇ (q38 ◇ ((q37 ◇ q38) ◇ q37))) (apc17 q37 q38))
  have apc40 : forall (q39 q40:G), (q40 ◇ (q40 ◇ (q40 ◇ ((q39 ◇ q40) ◇ q39)))) = (q40 ◇ ((q39 ◇ q40) ◇ q39)):=by
    intro q39 q40
    exact ((((cg (fun t => (q40 ◇ ((q40 ◇ (q40 ◇ ((q39 ◇ q40) ◇ q39))) ◇ q40)) ◇ t) (apc39 q39 q40)).trans (apc14 (q40 ◇ ((q39 ◇ q40) ◇ q39)) q40)).symm).trans (((cg (fun t => t ◇ (q40 ◇ (q40 ◇ (q40 ◇ (q40 ◇ ((q39 ◇ q40) ◇ q39)))))) (cg (fun t => q40 ◇ t) (cg (fun t => t ◇ q40) (apc39 q39 q40)))).symm).trans (apc14 (q40 ◇ (q40 ◇ (q40 ◇ ((q39 ◇ q40) ◇ q39)))) q40))).symm
  have apc41 : forall (q35 q36 q39 q40:G), ((q35 ◇ ((q36 ◇ q35) ◇ q36)) ◇ q35) = (q35 ◇ q35):=by
    intro q35 q36 q39 q40
    exact ((cg (fun t => t ◇ q35) (apc40 q36 q35)).symm).trans (apc25 q35 q36)
  have apc48 : forall (q41 q42 q43:G), ((q42 ◇ (q43 ◇ q43)) ◇ (q42 ◇ ((q41 ◇ q43) ◇ q41))) = ((q41 ◇ q43) ◇ q41):=by
    intro q41 q42 q43
    exact ((cg (fun t => t ◇ (q42 ◇ ((q41 ◇ q43) ◇ q41))) (cg (fun t => q42 ◇ t) (apc41 q43 q41 q41 q41))).symm).trans ((h ((q41 ◇ q43) ◇ q41) q42 q43).symm)
  have apc49 : forall (q44 q45:G), (q45 ◇ (q45 ◇ ((q44 ◇ q45) ◇ q44))) = ((q44 ◇ q45) ◇ q44):=by
    intro q44 q45
    exact ((cg (fun t => t ◇ (q45 ◇ ((q44 ◇ q45) ◇ q44))) (apc15 q45)).symm).trans (apc48 q44 q45 q45)
  have apc54 : forall (q46 q47 q48:G), ((q48 ◇ ((q47 ◇ q46) ◇ q47)) ◇ (q48 ◇ (q46 ◇ q46))) = (q46 ◇ q46):=by
    intro q46 q47 q48
    exact ((cg (fun t => t ◇ (q48 ◇ (q46 ◇ q46))) (cg (fun t => q48 ◇ t) (apc49 q47 q46))).symm).trans (apc4 q46 q46 q47 q48)
  have apc55 : forall (q49 q50 q51:G), ((q51 ◇ (q49 ◇ q49)) ◇ ((q50 ◇ q49) ◇ q50)) = (q51 ◇ ((q50 ◇ q49) ◇ q50)):=by
    intro q49 q50 q51
    exact (((cg (fun t => (q51 ◇ (q49 ◇ q49)) ◇ t) (cg (fun t => t ◇ (q51 ◇ ((q50 ◇ q49) ◇ q50))) (apc19 q51 q49))).trans (cg (fun t => (q51 ◇ (q49 ◇ q49)) ◇ t) (apc48 q50 q51 q49))).symm).trans (((cg (fun t => (q51 ◇ (q49 ◇ q49)) ◇ t) (cg (fun t => t ◇ (q51 ◇ ((q50 ◇ q49) ◇ q50))) (cg (fun t => (q51 ◇ (q49 ◇ q49)) ◇ t) (apc54 q49 q50 q51)))).symm).trans (apc9 q49 (q51 ◇ ((q50 ◇ q49) ◇ q50)) (q51 ◇ (q49 ◇ q49)) q49 q49 q49))
  have apc56 : forall (q52 q53:G), ((q52 ◇ (q53 ◇ q53)) ◇ q53) = (q52 ◇ q53):=by
    intro q52 q53
    exact ((((cg (fun t => t ◇ q53) (cg (fun t => (q52 ◇ ((q52 ◇ q53) ◇ q52)) ◇ t) (cg (fun t => q53 ◇ t) (apc55 q53 q52 q52)))).trans (apc5 q52 q53 q52 q52)).symm).trans (((cg (fun t => t ◇ q53) (cg (fun t => t ◇ (q53 ◇ ((q52 ◇ (q53 ◇ q53)) ◇ ((q52 ◇ q53) ◇ q52)))) (apc55 q53 q52 q52))).symm).trans (apc5 q52 q53 (q52 ◇ (q53 ◇ q53)) q52))).symm
  have apc57 : forall (q54 q55:G), ((q54 ◇ ((q55 ◇ q55) ◇ (q55 ◇ q55))) ◇ q55) = (q54 ◇ q55):=by
    intro q54 q55
    exact (((apc56 q54 q55).symm).trans (((cg (fun t => t ◇ q55) (apc56 q54 (q55 ◇ q55))).symm).trans (apc56 (q54 ◇ ((q55 ◇ q55) ◇ (q55 ◇ q55))) q55))).symm
  have apc58 : forall (q56:G), ((q56 ◇ q56) ◇ q56) = (q56 ◇ q56):=by
    intro q56
    exact (((cg (fun t => t ◇ q56) (apc4 q56 q56 q56 (q56 ◇ q56))).symm).trans (apc57 ((q56 ◇ q56) ◇ (q56 ◇ (q56 ◇ ((q56 ◇ q56) ◇ q56)))) q56)).trans (((cg (fun t => t ◇ q56) (cg (fun t => (q56 ◇ q56) ◇ t) (apc49 q56 q56))).trans (apc8 q56 q56 q56)).trans (cg (fun t => t ◇ q56) (apc15 q56)))
  have apc59 : forall (q26 q56:G), ((q26 ◇ q26) ◇ (q26 ◇ q26)) = q26:=by
    intro q26 q56
    exact (((cg (fun t => (q26 ◇ q26) ◇ t) (cg (fun t => t ◇ q26) (apc58 q26))).trans (cg (fun t => (q26 ◇ q26) ◇ t) (apc58 q26))).symm).trans (apc16 q26)
  have apc60 : forall (q57 q58:G), (q57 ◇ (q58 ◇ q58)) = q58:=by
    intro q57 q58
    exact ((((cg (fun t => (q58 ◇ q58) ◇ t) (apc18 q57 q58)).trans (apc59 q58 ((q58 ◇ q58) ◇ (q58 ◇ q58)))).symm).trans (((cg (fun t => t ◇ ((q57 ◇ (q58 ◇ q58)) ◇ (q57 ◇ (q58 ◇ q58)))) (apc18 q57 q58)).symm).trans (apc59 (q57 ◇ (q58 ◇ q58)) q57))).symm
  have apc61 : forall (q57 q58 q52 q53:G), (q53 ◇ q53) = (q52 ◇ q53):=by
    intro q57 q58 q52 q53
    exact ((cg (fun t => t ◇ q53) (apc60 q52 q53)).symm).trans (apc56 q52 q53)
  have apc65 : forall (q59 q60:G), ((q60 ◇ q59) ◇ q60) = (q60 ◇ q60):=by
    intro q59 q60
    exact ((cg (fun t => t ◇ q60) (cg (fun t => q60 ◇ t) (apc60 ((q59 ◇ q59) ◇ q60) q59))).symm).trans (apc41 q60 (q59 ◇ q59) q59 q59)
  have apc66 : forall (q61 q62 q63:G), (q63 ◇ (q62 ◇ q61)) = q61:=by
    intro q61 q62 q63
    exact ((cg (fun t => t ◇ (q62 ◇ q61)) (apc60 q62 q63)).symm).trans (((cg (fun t => t ◇ (q62 ◇ q61)) (cg (fun t => q62 ◇ t) ((apc61 q61 q61 (q63 ◇ q61) q63).symm))).symm).trans ((h q61 q62 q63).symm))
  have apc67 : forall (q64 q65:G), ((q64 ◇ q64) ◇ q65) = (q65 ◇ q65):=by
    intro q64 q65
    exact ((cg (fun t => t ◇ q65) ((apc61 q64 q64 q65 q64).symm)).symm).trans (apc65 q64 q65)
  exact (calc
    x = x:=rfl
    _ = ((y ◇ y) ◇ (((z ◇ y) ◇ z) ◇ x)):=(((cg (fun t => (y ◇ y) ◇ t) (cg (fun t => t ◇ x) (apc65 y z))).trans (cg (fun t => (y ◇ y) ◇ t) (apc67 z x))).trans (apc66 x x (y ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_26286_to_20934 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_26286_to_20934
