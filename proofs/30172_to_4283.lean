-- Equation30172 → Equation4283
-- Recorded verdict: true
-- Premise: x = (x ◇ (x ◇ ((y ◇ z) ◇ z))) ◇ y
-- Conclusion: x ◇ (x ◇ y) = x ◇ (y ◇ x)
-- Original submission SHA-256: 1c5e2a0c3aa5de31552a8ae05fa7cd7ba7979c67fce59e1ce36f5a60c9da4ce8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (x ◇ ((y ◇ z) ◇ z))) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ y) = x ◇ (y ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc2:=fun (q0 q1 q2 q3:G)=>by
    exact ((cg (fun t => t ◇ (q0 ◇ (q0 ◇ ((q3 ◇ q1) ◇ q1)))) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q3) ((h q0 q3 q1).symm))))).symm).trans ((h q2 (q0 ◇ (q0 ◇ ((q3 ◇ q1) ◇ q1))) q3).symm)
  have apc3:=fun (q0 q1 q4 q3:G)=>by
    exact ((cg (fun t => t ◇ q4) (cg (fun t => (q0 ◇ (q0 ◇ ((((q4 ◇ q3) ◇ q3) ◇ q1) ◇ q1))) ◇ t) ((h q0 ((q4 ◇ q3) ◇ q3) q1).symm))).symm).trans ((h (q0 ◇ (q0 ◇ ((((q4 ◇ q3) ◇ q3) ◇ q1) ◇ q1))) q4 q3).symm)
  have apc4:=fun (q5 q6 q7:G)=>by
    exact (((cg (fun t => t ◇ q6) ((h ((q6 ◇ q7) ◇ q7) ((q6 ◇ q7) ◇ q7) q5).symm)).symm).trans (apc3 ((q6 ◇ q7) ◇ q7) q5 q6 q7)).symm
  have apc5:=fun (q8 q9:G)=>by
    exact ((cg (fun t => t ◇ ((q8 ◇ q9) ◇ q9)) (apc4 q8 q8 q9)).symm).trans ((h ((q8 ◇ q9) ◇ q9) ((q8 ◇ q9) ◇ q9) q8).symm)
  have apc19:=fun (q10 q11 q12 q13 q14:G)=>by
    exact ((cg (fun t => t ◇ (q12 ◇ (q12 ◇ ((q14 ◇ q13) ◇ q13)))) (cg (fun t => (q10 ◇ (q10 ◇ (((q12 ◇ q14) ◇ q11) ◇ q11))) ◇ t) ((h q10 (q12 ◇ q14) q11).symm))).symm).trans (apc2 q12 q13 (q10 ◇ (q10 ◇ (((q12 ◇ q14) ◇ q11) ◇ q11))) q14)
  have apc33:=fun (q15 q16 q17 q18 q19:G)=>by
    exact ((cg (fun t => t ◇ (q18 ◇ (q18 ◇ (((q18 ◇ ((q17 ◇ q15) ◇ q15)) ◇ q19) ◇ q19)))) (cg (fun t => (q16 ◇ (q16 ◇ (q18 ◇ q17))) ◇ t) (apc2 q18 q15 q16 q17))).symm).trans (apc2 q18 q19 (q16 ◇ (q16 ◇ (q18 ◇ q17))) (q18 ◇ ((q17 ◇ q15) ◇ q15)))
  have apc34:=fun (q20 q21 q22 q23:G)=>by
    exact ((cg (fun t => t ◇ ((q21 ◇ q22) ◇ ((q21 ◇ q22) ◇ ((((q21 ◇ q22) ◇ ((q22 ◇ q20) ◇ q20)) ◇ q23) ◇ q23)))) ((h q21 q21 q22).symm)).symm).trans (apc33 q20 q21 q22 (q21 ◇ q22) q23)
  have apc38:=fun (q24 q25 q26 q5 q7:G)=>by
    exact (((apc19 q26 q5 q24 q25 q7).symm).trans (((cg (fun t => t ◇ (q24 ◇ (q24 ◇ ((q7 ◇ q25) ◇ q25)))) (cg (fun t => t ◇ q26) (cg (fun t => q26 ◇ t) (cg (fun t => q26 ◇ t) (cg (fun t => t ◇ q5) (cg (fun t => t ◇ q5) (cg (fun t => t ◇ q7) ((h q24 q7 q25).symm)))))))).symm).trans (apc3 q26 q5 (q24 ◇ (q24 ◇ ((q7 ◇ q25) ◇ q25))) q7))).symm
  have apc39:=fun (q27 q28 q29 q30 q31:G)=>by
    exact ((cg (fun t => t ◇ (((q27 ◇ (q27 ◇ ((q29 ◇ q28) ◇ q28))) ◇ q29) ◇ q29)) (apc38 q27 q28 q30 q31 q29)).symm).trans ((h q30 (((q27 ◇ (q27 ◇ ((q29 ◇ q28) ◇ q28))) ◇ q29) ◇ q29) q31).symm)
  have apc40:=fun (q32 q33 q34 q35:G)=>by
    exact ((cg (fun t => (q34 ◇ (q34 ◇ (((q32 ◇ q33) ◇ q35) ◇ q35))) ◇ t) (cg (fun t => t ◇ q33) ((h q32 q33 q32).symm))).symm).trans (apc39 q32 q32 q33 q34 q35)
  have apc112:=fun (q10 q11 q13 q36 q14:G)=>by
    exact ((cg (fun t => t ◇ ((q10 ◇ (q10 ◇ ((q14 ◇ q11) ◇ q11))) ◇ ((q10 ◇ (q10 ◇ ((q14 ◇ q11) ◇ q11))) ◇ ((q14 ◇ q13) ◇ q13)))) (cg (fun t => q36 ◇ t) (cg (fun t => q36 ◇ t) ((h q10 q14 q11).symm)))).symm).trans (apc2 (q10 ◇ (q10 ◇ ((q14 ◇ q11) ◇ q11))) q13 q36 q14)
  have apc113:=fun (q37 q38 q39 q40 q41 q42:G)=>by
    exact ((cg (fun t => (q42 ◇ (q42 ◇ q39)) ◇ t) (cg (fun t => (q39 ◇ (q39 ◇ (((q41 ◇ (q41 ◇ ((((q41 ◇ q38) ◇ q38) ◇ q37) ◇ q37))) ◇ q40) ◇ q40))) ◇ t) (apc40 q41 (q41 ◇ ((((q41 ◇ q38) ◇ q38) ◇ q37) ◇ q37)) q39 q40))).symm).trans (((cg (fun t => (q42 ◇ (q42 ◇ q39)) ◇ t) (cg (fun t => (q39 ◇ (q39 ◇ (((q41 ◇ (q41 ◇ ((((q41 ◇ q38) ◇ q38) ◇ q37) ◇ q37))) ◇ q40) ◇ q40))) ◇ t) (cg (fun t => (q39 ◇ (q39 ◇ (((q41 ◇ (q41 ◇ ((((q41 ◇ q38) ◇ q38) ◇ q37) ◇ q37))) ◇ q40) ◇ q40))) ◇ t) (apc3 q41 q37 q41 q38)))).symm).trans (apc112 q39 q40 q41 q42 (q41 ◇ (q41 ◇ ((((q41 ◇ q38) ◇ q38) ◇ q37) ◇ q37)))))
  have apc114:=fun (q43 q44 q45 q46:G)=>by
    exact ((cg (fun t => (q46 ◇ (q46 ◇ q44)) ◇ t) (cg (fun t => t ◇ q44) (cg (fun t => q44 ◇ t) (cg (fun t => q44 ◇ t) (cg (fun t => t ◇ ((q45 ◇ q43) ◇ q43)) ((h q45 ((q45 ◇ q43) ◇ q43) q43).symm)))))).symm).trans (apc113 q43 q43 q44 ((q45 ◇ q43) ◇ q43) q45 q46)
  have apc131:=fun (q47 q48 q49 q50 q51:G)=>by
    exact ((cg (fun t => (q51 ◇ (q51 ◇ q50)) ◇ t) (cg (fun t => t ◇ q50) (cg (fun t => q50 ◇ t) (cg (fun t => q50 ◇ t) (cg (fun t => (q47 ◇ (q47 ◇ ((q49 ◇ q48) ◇ q48))) ◇ t) (cg (fun t => t ◇ q49) ((h q47 q49 q48).symm))))))).symm).trans (apc114 q49 q50 (q47 ◇ (q47 ◇ ((q49 ◇ q48) ◇ q48))) q51)
  have apc132:=fun (q52 q53 q54 q55:G)=>by
    exact ((cg (fun t => (q55 ◇ (q55 ◇ q54)) ◇ t) (cg (fun t => t ◇ q54) (cg (fun t => q54 ◇ t) (cg (fun t => q54 ◇ t) (apc40 (q52 ◇ q53) q53 (((q52 ◇ q53) ◇ q53) ◇ q52) q52))))).symm).trans (((cg (fun t => (q55 ◇ (q55 ◇ q54)) ◇ t) (cg (fun t => t ◇ q54) (cg (fun t => q54 ◇ t) (cg (fun t => q54 ◇ t) (cg (fun t => ((((q52 ◇ q53) ◇ q53) ◇ q52) ◇ ((((q52 ◇ q53) ◇ q53) ◇ q52) ◇ ((((q52 ◇ q53) ◇ q53) ◇ q52) ◇ q52))) ◇ t) (apc5 q52 q53)))))).symm).trans (apc131 (((q52 ◇ q53) ◇ q53) ◇ q52) q52 ((q52 ◇ q53) ◇ q53) q54 q55))
  have apc133:=fun (q56 q57:G)=>by
    exact ((cg (fun t => (q57 ◇ (q57 ◇ (q56 ◇ q56))) ◇ t) ((h (q56 ◇ q56) (q56 ◇ q56) q56).symm)).symm).trans (apc132 q56 q56 (q56 ◇ q56) q57)
  have apc147:=fun (q58 q59 q60:G)=>by
    exact ((cg (fun t => t ◇ (q59 ◇ (q59 ◇ (q58 ◇ q58)))) (cg (fun t => q60 ◇ t) (cg (fun t => q60 ◇ t) (cg (fun t => t ◇ (q58 ◇ q58)) (apc133 q58 q59))))).symm).trans ((h q60 (q59 ◇ (q59 ◇ (q58 ◇ q58))) (q58 ◇ q58)).symm)
  have apc148:=fun (q61:G)=>by
    exact ((cg (fun t => (q61 ◇ q61) ◇ t) (apc147 q61 q61 q61)).symm).trans ((((cg (fun t => t ◇ ((q61 ◇ (q61 ◇ (q61 ◇ (q61 ◇ q61)))) ◇ (q61 ◇ (q61 ◇ (q61 ◇ q61))))) (cg (fun t => t ◇ q61) (apc147 q61 q61 q61))).symm).trans (apc5 q61 (q61 ◇ (q61 ◇ (q61 ◇ q61))))).trans (apc147 q61 q61 q61))
  have apc149:=fun (q62 q63:G)=>by
    exact ((cg (fun t => t ◇ q63) (cg (fun t => q62 ◇ t) (cg (fun t => q62 ◇ t) (apc147 q62 q63 q63)))).symm).trans ((h q62 q63 (q63 ◇ (q63 ◇ (q62 ◇ q62)))).symm)
  have apc150:=fun (q64:G)=>by
    exact (((((cg (fun t => q64 ◇ t) (cg (fun t => (q64 ◇ q64) ◇ t) (cg (fun t => (q64 ◇ q64) ◇ t) (apc148 q64)))).trans (cg (fun t => q64 ◇ t) (cg (fun t => (q64 ◇ q64) ◇ t) (apc148 q64)))).trans (cg (fun t => q64 ◇ t) (apc148 q64))).symm).trans ((((cg (fun t => q64 ◇ t) (cg (fun t => (q64 ◇ q64) ◇ t) (cg (fun t => (q64 ◇ q64) ◇ t) (cg (fun t => t ◇ q64) (apc149 (q64 ◇ q64) q64))))).symm).trans (apc34 q64 q64 q64 q64)).trans (cg (fun t => q64 ◇ t) (cg (fun t => q64 ◇ t) (apc148 q64))))).symm
  have apc151:=fun (q65:G)=>by
    exact ((cg (fun t => t ◇ (q65 ◇ q65)) (apc150 q65)).symm).trans (((cg (fun t => t ◇ (q65 ◇ q65)) (cg (fun t => q65 ◇ t) (apc150 q65))).symm).trans (apc149 q65 (q65 ◇ q65)))
  have apc152:=fun (q66 q67:G)=>by
    exact (((cg (fun t => q67 ◇ t) (cg (fun t => ((q67 ◇ (q67 ◇ (q67 ◇ (q66 ◇ q66)))) ◇ (q67 ◇ (q67 ◇ (q66 ◇ q66)))) ◇ t) (cg (fun t => t ◇ q66) (cg (fun t => t ◇ q66) (apc147 q66 q67 q67))))).trans (cg (fun t => q67 ◇ t) (cg (fun t => t ◇ ((q67 ◇ q66) ◇ q66)) (apc147 q66 q67 q67)))).symm).trans ((((cg (fun t => t ◇ (((q67 ◇ (q67 ◇ (q67 ◇ (q66 ◇ q66)))) ◇ (q67 ◇ (q67 ◇ (q66 ◇ q66)))) ◇ ((((q67 ◇ (q67 ◇ (q67 ◇ (q66 ◇ q66)))) ◇ (q67 ◇ (q67 ◇ (q66 ◇ q66)))) ◇ q66) ◇ q66))) (apc147 q66 q67 q67)).symm).trans (apc4 q66 q67 (q67 ◇ (q67 ◇ (q66 ◇ q66))))).trans (cg (fun t => t ◇ q67) (apc147 q66 q67 q67)))
  have apc153:=fun (q68 q69:G)=>by
    exact ((cg (fun t => t ◇ ((q69 ◇ q68) ◇ q68)) (apc152 q68 q69)).symm).trans (apc149 q69 ((q69 ◇ q68) ◇ q68))
  have apc154:=fun (q70 q71:G)=>by
    exact ((cg (fun t => t ◇ ((q71 ◇ q70) ◇ q70)) (apc148 q71)).symm).trans (((cg (fun t => t ◇ ((q71 ◇ q70) ◇ q70)) (cg (fun t => (q71 ◇ q71) ◇ t) (apc153 q70 q71))).symm).trans (apc149 (q71 ◇ q71) ((q71 ◇ q70) ◇ q70)))
  have apc156:=fun (q72 q73:G)=>by
    exact ((cg (fun t => t ◇ q73) (cg (fun t => (q72 ◇ (q72 ◇ q73)) ◇ t) (apc149 q72 q73))).symm).trans (apc149 (q72 ◇ (q72 ◇ q73)) q73)
  have apc160:=fun (q74 q75 q76:G)=>by
    exact ((cg (fun t => (q75 ◇ (q75 ◇ (q74 ◇ q76))) ◇ t) (cg (fun t => q74 ◇ t) (cg (fun t => q74 ◇ t) (apc147 q74 q76 q76)))).symm).trans (apc2 q74 (q76 ◇ (q76 ◇ (q74 ◇ q74))) q75 q76)
  have apc164:=fun (q77 q78:G)=>by
    exact (((cg (fun t => t ◇ q77) (apc148 ((q77 ◇ q78) ◇ q78))).symm).trans (((cg (fun t => t ◇ q77) (cg (fun t => (((q77 ◇ q78) ◇ q78) ◇ ((q77 ◇ q78) ◇ q78)) ◇ t) (apc148 ((q77 ◇ q78) ◇ q78)))).symm).trans ((h (((q77 ◇ q78) ◇ q78) ◇ ((q77 ◇ q78) ◇ q78)) q77 q78).symm))).symm
  have apc169:=fun (q79 q80:G)=>by
    exact (((cg (fun t => (q79 ◇ (q79 ◇ q80)) ◇ t) (cg (fun t => t ◇ q80) (apc149 q79 q80))).symm).trans (apc154 q80 (q79 ◇ (q79 ◇ q80)))).symm
  have apc170:=fun (q81 q82:G)=>by
    exact (((cg (fun t => ((q81 ◇ (q81 ◇ q82)) ◇ (q81 ◇ q82)) ◇ t) (apc169 q81 q82)).trans (apc164 q81 (q81 ◇ q82))).symm).trans (((cg (fun t => t ◇ ((q81 ◇ (q81 ◇ q82)) ◇ (q81 ◇ (q81 ◇ q82)))) (apc169 q81 q82)).symm).trans (apc151 (q81 ◇ (q81 ◇ q82))))
  have apc171:=fun (q83 q84:G)=>by
    exact (((cg (fun t => t ◇ q84) (apc160 q84 q84 q83)).symm).trans (apc170 q84 (q84 ◇ q83))).symm
  have apc172:=fun (q85 q86:G)=>by
    exact ((cg (fun t => t ◇ (q86 ◇ q85)) (apc148 q86)).symm).trans ((((cg (fun t => t ◇ (q86 ◇ q85)) (cg (fun t => t ◇ q86) (apc171 q85 q86))).symm).trans (apc156 q86 (q86 ◇ q85))).trans (apc171 q85 q86))
  have apc173:=fun (x y z q85 q86:G)=>by
    exact ((h x y x).trans (cg (fun t => t ◇ y) (apc172 ((y ◇ x) ◇ x) x))).symm
  have apc174:=fun (q87 q88:G)=>by
    exact ((cg (fun t => t ◇ q88) (apc173 q87 ((q87 ◇ q87) ◇ ((q88 ◇ q87) ◇ q87)) q87 q87 q87)).symm).trans ((h (q87 ◇ q87) q88 q87).symm)
  exact (apc174 x (x ◇ y)).trans ((apc174 x (y ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_30172_to_4283 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_30172_to_4283
