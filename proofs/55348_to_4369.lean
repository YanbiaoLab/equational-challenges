-- Equation55348 → Equation4369
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ z) = z ◇ ((x ◇ y) ◇ y)
-- Conclusion: x ◇ (y ◇ z) = z ◇ (y ◇ x)
-- Original submission SHA-256: 5f43893f4fe61b05b004d0530d6f18e50da01472dba4367b5fbe618ef837824d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = z ◇ ((x ◇ y) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = z ◇ (y ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc0:=fun (q0 q1 q2 q3:G)=>by
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ q1)) ((h q0 q1 q2).symm))).symm).trans ((h q2 ((q0 ◇ q1) ◇ q1) q3).symm)
  have apc1:=fun (q4 q5 q6 q7:G)=>by
    exact ((cg (fun t => q7 ◇ t) ((h q4 q5 (q4 ◇ (q5 ◇ q6))).symm)).symm).trans (apc0 q4 q5 q6 q7)
  have apc2:=fun (q0 q1 q2 q3:G)=>by
    exact ((cg (fun t => q3 ◇ t) ((h q0 q1 (q2 ◇ ((q0 ◇ q1) ◇ q1))).symm)).symm).trans ((h q2 ((q0 ◇ q1) ◇ q1) q3).symm)
  have apc3:=fun (q8 q9 q10 q11:G)=>by
    exact ((cg (fun t => q11 ◇ t) (apc1 q10 q9 q8 q9)).symm).trans (apc1 q9 q10 (q9 ◇ q8) q11)
  have apc4:=fun (q12 q13 q14 q15:G)=>by
    exact (((cg (fun t => q15 ◇ t) ((h (q14 ◇ q13) q13 q12).symm)).symm).trans (apc3 q12 q13 q14 q15)).symm
  have apc5:=fun (q16 q17 q18:G)=>by
    exact (((apc4 q16 q17 q18 q18).symm).trans ((h (q17 ◇ q18) q18 (q17 ◇ q16)).symm)).symm
  have apc6:=fun (q12 q13 q14 q15 q8 q9 q10 q11:G)=>by
    exact (apc3 q8 q9 q10 q11).trans (apc4 q8 q9 q10 q11)
  have apc8:=fun (q19 q20 q21:G)=>by
    exact (((apc6 (q21 ◇ (q20 ◇ (((q20 ◇ q19) ◇ q19) ◇ q19))) (q21 ◇ (q20 ◇ (((q20 ◇ q19) ◇ q19) ◇ q19))) (q21 ◇ (q20 ◇ (((q20 ◇ q19) ◇ q19) ◇ q19))) (q21 ◇ (q20 ◇ (((q20 ◇ q19) ◇ q19) ◇ q19))) q20 q19 q20 q21).symm).trans (((cg (fun t => q21 ◇ t) (apc2 q20 q19 q20 q19)).symm).trans (apc1 q19 q20 ((q20 ◇ q19) ◇ q19) q21))).symm
  have apc11:=fun (q22 q23 q24 q25:G)=>by
    exact (((cg (fun t => q25 ◇ t) (apc4 q22 q24 q23 q23)).symm).trans (apc6 q22 q22 q22 q22 (q24 ◇ q22) q23 q24 q25)).symm
  have apc12:=fun (q26 q27 q28 q29:G)=>by
    exact ((cg (fun t => q29 ◇ t) (cg (fun t => q27 ◇ t) (cg (fun t => (q26 ◇ q28) ◇ t) ((h q26 q28 q27).symm)))).symm).trans (apc1 q27 (q26 ◇ q28) q28 q29)
  have apc13:=fun (q30 q31 q32:G)=>by
    exact (((cg (fun t => ((q30 ◇ q31) ◇ q32) ◇ t) ((h q30 q31 q32).symm)).symm).trans (apc5 q31 (q30 ◇ q31) q32)).symm
  have apc14:=fun (q33:G)=>by
    exact ((apc13 q33 q33 q33).symm).trans (apc0 q33 q33 q33 q33)
  have apc16:=fun (q26 q34 q27 q35 q29:G)=>by
    exact ((cg (fun t => q29 ◇ t) (cg (fun t => q27 ◇ t) (cg (fun t => q35 ◇ t) (cg (fun t => q27 ◇ t) ((h q26 q34 q35).symm))))).symm).trans (apc1 q27 q35 ((q26 ◇ q34) ◇ q34) q29)
  have apc17:=fun (q36 q37 q38 q39:G)=>by
    exact ((apc16 q38 q36 q37 q38 q39).symm).trans (apc1 q37 q38 (q36 ◇ q38) q39)
  have apc18:=fun (q40 q41 q42:G)=>by
    exact (((apc17 q40 q41 q42 q42).symm).trans ((h (q41 ◇ q42) q42 ((q42 ◇ q40) ◇ q40)).symm)).symm
  have apc20:=fun (q43 q44 q45:G)=>by
    exact (((cg (fun t => (q44 ◇ q45) ◇ t) ((h q45 q43 q45).symm)).symm).trans (apc18 q43 q44 q45)).symm
  have apc21:=fun (q43 q44 q45 q40 q41 q42:G)=>by
    exact (apc18 q40 q41 q42).trans (apc20 q40 q41 q42)
  have apc22:=fun (q30 q46 q47 q32:G)=>by
    exact (((cg (fun t => (q47 ◇ q32) ◇ t) (cg (fun t => q32 ◇ t) ((h q30 q46 q47).symm))).symm).trans (apc5 ((q30 ◇ q46) ◇ q46) q47 q32)).symm
  have apc24:=fun (q48 q49 q50 q51:G)=>by
    exact (((cg (fun t => q51 ◇ t) (cg (fun t => (q51 ◇ q50) ◇ t) ((h q48 q49 q50).symm))).symm).trans (apc22 q48 q49 q50 q51)).symm
  have apc26:=fun (q52 q53 q54:G)=>by
    exact ((apc5 (q52 ◇ (q53 ◇ q54)) q53 q52).symm).trans (apc1 q52 q53 q54 (q53 ◇ q52))
  have apc28:=fun (q55 q56 q57 q58:G)=>by
    exact (((cg (fun t => q58 ◇ t) (apc6 (q56 ◇ (q55 ◇ (((q56 ◇ q57) ◇ q57) ◇ q57))) (q56 ◇ (q55 ◇ (((q56 ◇ q57) ◇ q57) ◇ q57))) (q56 ◇ (q55 ◇ (((q56 ◇ q57) ◇ q57) ◇ q57))) (q56 ◇ (q55 ◇ (((q56 ◇ q57) ◇ q57) ◇ q57))) q55 q57 q56 q56)).symm).trans (((cg (fun t => q58 ◇ t) (cg (fun t => q56 ◇ t) ((h q55 ((q56 ◇ q57) ◇ q57) q57).symm))).symm).trans (apc2 q56 q57 (q55 ◇ ((q56 ◇ q57) ◇ q57)) q58))).symm
  have apc29:=fun (q59 q60 q61:G)=>by
    exact (((apc28 q59 q60 q61 q61).symm).trans ((h (q60 ◇ q61) q61 (q59 ◇ ((q60 ◇ q61) ◇ q61))).symm)).symm
  have apc30:=fun (q62 q63 q64:G)=>by
    exact ((cg (fun t => (q63 ◇ q64) ◇ t) (cg (fun t => q64 ◇ t) ((h q63 q64 q62).symm))).symm).trans (apc29 q62 q63 q64)
  have apc33:=fun (q65 q66 q67:G)=>by
    exact ((cg (fun t => q65 ◇ t) (apc5 (q66 ◇ q67) q65 q66)).symm).trans (apc26 q65 q66 q67)
  have apc34:=fun (q68 q69 q70 q71 q72:G)=>by
    exact (((cg (fun t => t ◇ (((q70 ◇ q71) ◇ q71) ◇ q72)) ((h q68 q69 q70).symm)).symm).trans (apc4 ((q68 ◇ q69) ◇ q69) q70 q71 q72)).symm
  have apc35:=fun (q73 q74 q75 q76 q77:G)=>by
    exact (((cg (fun t => q77 ◇ t) (cg (fun t => (q76 ◇ q75) ◇ t) ((h q73 q74 q75).symm))).symm).trans (apc34 q73 q74 q75 q76 q77)).symm
  have apc36:=fun (q73 q74 q75 q76 q77 q68 q69 q70 q71 q72:G)=>by
    exact (apc34 q68 q69 q70 q71 q72).trans (apc35 q68 q69 q70 q71 q72)
  have apc37:=fun (q68 q69 q78 q70 q71:G)=>by
    exact ((cg (fun t => (q70 ◇ q78) ◇ t) ((h q68 q69 ((q70 ◇ q71) ◇ q71)).symm)).symm).trans (apc4 q78 q70 q71 ((q68 ◇ q69) ◇ q69))
  have apc38:=fun (q68 q69 q78 q70 q71 q59 q60 q61:G)=>by
    exact ((apc37 q61 q59 q61 q60 q61).symm).trans (apc29 q59 q60 q61)
  have apc39:=fun (q79 q80 q81 q82 q83:G)=>by
    exact (((cg (fun t => (q82 ◇ q81) ◇ t) (cg (fun t => q79 ◇ t) ((h q82 q83 q80).symm))).symm).trans (apc37 q79 q80 q81 q82 q83)).symm
  have apc40:=fun (q79 q80 q81 q82 q83 q68 q69 q78 q70 q71:G)=>by
    exact (apc37 q68 q69 q78 q70 q71).trans (apc39 q68 q69 q78 q70 q71)
  have apc43:=fun (q84 q85 q86:G)=>by
    exact ((apc17 q84 (q85 ◇ q84) q85 q86).symm).trans (apc4 q84 (q85 ◇ q84) q85 q86)
  have apc48:=fun (q87 q88 q89 q90:G)=>by
    exact (((cg (fun t => (q89 ◇ q90) ◇ t) (cg (fun t => q90 ◇ t) ((h q87 q89 q88).symm))).symm).trans (apc24 q88 (q87 ◇ q89) q89 q90)).symm
  have apc49:=fun (q91 q92 q93 q94:G)=>by
    exact (((cg (fun t => q94 ◇ t) (cg (fun t => (q94 ◇ q93) ◇ t) ((h q91 q93 q92).symm))).symm).trans (apc48 q91 q92 q93 q94)).symm
  have apc50:=fun (q95 q96:G)=>by
    exact (((cg (fun t => q96 ◇ t) (apc21 q95 q95 q95 q95 q96 q95)).symm).trans (apc48 q95 q95 q95 q96)).symm
  have apc51:=fun (q97:G)=>by
    exact ((apc50 q97 q97).symm).trans (apc30 q97 q97 q97)
  have apc52:=fun (q98 q99 q100:G)=>by
    exact ((cg (fun t => q98 ◇ t) (cg (fun t => q99 ◇ t) (apc5 q100 q99 q98))).symm).trans (apc33 q98 q99 q100)
  have apc53:=fun (q101 q102 q103:G)=>by
    exact ((cg (fun t => q103 ◇ t) (cg (fun t => q102 ◇ t) (apc5 q102 q101 q101))).symm).trans (apc12 q101 q102 q101 q103)
  have apc54:=fun (q104 q105 q106 q107:G)=>by
    exact (((cg (fun t => ((q107 ◇ q106) ◇ q106) ◇ t) ((h q104 q105 ((q106 ◇ q107) ◇ q107)).symm)).symm).trans (apc8 q106 q107 ((q104 ◇ q105) ◇ q105))).trans (apc39 q104 q105 q107 q106 q107)
  have apc55:=fun (q108 q109 q110 q111:G)=>by
    exact ((cg (fun t => ((q111 ◇ q110) ◇ q110) ◇ t) (cg (fun t => q108 ◇ t) ((h q110 q111 q109).symm))).symm).trans (apc54 q108 q109 q110 q111)
  have apc56:=fun (q112 q113 q114:G)=>by
    exact (((apc1 q112 q113 q114 (q113 ◇ q112)).symm).trans (((apc55 q112 (q113 ◇ q114) q113 q112).symm).trans (apc1 q112 q113 q114 ((q112 ◇ q113) ◇ q113)))).symm
  have apc57:=fun (q115 q116 q117:G)=>by
    exact (((cg (fun t => q117 ◇ t) ((h q115 q116 ((q115 ◇ q116) ◇ q116)).symm)).symm).trans (apc56 q115 q116 q117)).symm
  have apc58:=fun (q118 q119 q120:G)=>by
    exact ((apc40 ((q119 ◇ q118) ◇ (q119 ◇ (q120 ◇ ((q119 ◇ q120) ◇ q120)))) ((q119 ◇ q118) ◇ (q119 ◇ (q120 ◇ ((q119 ◇ q120) ◇ q120)))) ((q119 ◇ q118) ◇ (q119 ◇ (q120 ◇ ((q119 ◇ q120) ◇ q120)))) ((q119 ◇ q118) ◇ (q119 ◇ (q120 ◇ ((q119 ◇ q120) ◇ q120)))) ((q119 ◇ q118) ◇ (q119 ◇ (q120 ◇ ((q119 ◇ q120) ◇ q120)))) q119 q120 q118 q119 q120).symm).trans (((apc57 q119 q120 (q119 ◇ q118)).symm).trans (apc4 q118 q119 q120 (q120 ◇ q119)))
  have apc61:=fun (q121:G)=>by
    exact ((apc58 q121 q121 q121).symm).trans (apc30 q121 q121 q121)
  have apc63:=fun (q122 q123 q124 q125:G)=>by
    exact (((cg (fun t => (q124 ◇ q123) ◇ t) (apc8 q125 q124 q122)).symm).trans (apc4 q123 q124 q125 (((q125 ◇ q124) ◇ q124) ◇ q122))).symm
  have apc74:=fun (q126 q127 q128 q129 q130:G)=>by
    exact (((cg (fun t => t ◇ (((q128 ◇ q129) ◇ q129) ◇ q130)) ((h q126 q128 q127).symm)).symm).trans (apc35 q127 (q126 ◇ q128) q128 q129 q130)).symm
  have apc75:=fun (q131 q132 q133 q134 q135:G)=>by
    exact (((cg (fun t => q135 ◇ t) (cg (fun t => (q134 ◇ q133) ◇ t) ((h q131 q133 q132).symm))).symm).trans (apc74 q131 q132 q133 q134 q135)).symm
  have apc82:=fun (q136 q137 q138:G)=>by
    exact ((cg (fun t => ((q138 ◇ q137) ◇ q137) ◇ t) (apc5 q136 q138 q137)).symm).trans (apc55 (q138 ◇ q137) q136 q137 q138)
  have apc90:=fun (q139 q140 q141:G)=>by
    exact (((cg (fun t => ((q141 ◇ q140) ◇ q140) ◇ t) (apc8 q141 q140 q139)).symm).trans (apc8 q140 q141 (((q141 ◇ q140) ◇ q140) ◇ q139))).trans (apc63 q139 q141 q140 q141)
  have apc91:=fun (q142:G)=>by
    exact (((apc90 q142 q142 q142).symm).trans (apc5 (q142 ◇ q142) (q142 ◇ q142) q142)).symm
  have apc93:=fun (q143 q144:G)=>by
    exact (((apc6 ((q144 ◇ q143) ◇ (q144 ◇ (((q144 ◇ q144) ◇ q144) ◇ q144))) ((q144 ◇ q143) ◇ (q144 ◇ (((q144 ◇ q144) ◇ q144) ◇ q144))) ((q144 ◇ q143) ◇ (q144 ◇ (((q144 ◇ q144) ◇ q144) ◇ q144))) ((q144 ◇ q143) ◇ (q144 ◇ (((q144 ◇ q144) ◇ q144) ◇ q144))) q144 q144 q144 (q144 ◇ q143)).symm).trans (((cg (fun t => (q144 ◇ q143) ◇ t) (apc14 q144)).symm).trans (apc4 q143 q144 q144 (q144 ◇ (q144 ◇ q144))))).symm
  have apc94:=fun (q87 q145 q89 q90:G)=>by
    exact (((cg (fun t => (q89 ◇ q90) ◇ t) ((h q87 (q145 ◇ q89) q90).symm)).symm).trans (apc24 (q87 ◇ (q145 ◇ q89)) q145 q89 q90)).symm
  have apc95:=fun (q146 q147 q148 q149:G)=>by
    exact (((cg (fun t => q149 ◇ t) ((h q146 (q147 ◇ q148) (q149 ◇ q148)).symm)).symm).trans (apc94 q146 q147 q148 q149)).symm
  have apc96:=fun (q150 q151 q152:G)=>by
    exact (((cg (fun t => (q152 ◇ q152) ◇ t) ((h q151 q152 q150).symm)).symm).trans (apc95 q150 q151 q152 q152)).symm
  have apc97:=fun (q150 q151 q152 q97:G)=>by
    exact (apc51 q97).trans (apc96 q97 q97 q97)
  have apc98:=fun (q150 q151 q152 q121:G)=>by
    exact (apc61 q121).trans (apc96 q121 q121 q121)
  have apc105:=fun (q143 q144 q142:G)=>by
    exact ((((cg (fun t => q142 ◇ t) (apc98 ((q142 ◇ q142) ◇ ((q142 ◇ q142) ◇ (q142 ◇ q142))) ((q142 ◇ q142) ◇ ((q142 ◇ q142) ◇ (q142 ◇ q142))) ((q142 ◇ q142) ◇ ((q142 ◇ q142) ◇ (q142 ◇ q142))) q142)).trans (apc97 (q142 ◇ ((q142 ◇ q142) ◇ (q142 ◇ (q142 ◇ q142)))) (q142 ◇ ((q142 ◇ q142) ◇ (q142 ◇ (q142 ◇ q142)))) (q142 ◇ ((q142 ◇ q142) ◇ (q142 ◇ (q142 ◇ q142)))) q142)).symm).trans (((cg (fun t => q142 ◇ t) (apc93 q142 q142)).symm).trans (apc91 q142))).symm
  have apc106:=fun (q153 q154:G)=>by
    exact (((cg (fun t => q154 ◇ t) (apc105 q153 q153 q153)).symm).trans (apc1 (q153 ◇ q153) q153 q153 q154)).symm
  have apc107:=fun (q155:G)=>by
    exact (((apc97 (q155 ◇ ((q155 ◇ q155) ◇ (q155 ◇ (q155 ◇ q155)))) (q155 ◇ ((q155 ◇ q155) ◇ (q155 ◇ (q155 ◇ q155)))) (q155 ◇ ((q155 ◇ q155) ◇ (q155 ◇ (q155 ◇ q155)))) q155).symm).trans (((apc106 q155 q155).symm).trans ((h ((q155 ◇ q155) ◇ q155) q155 q155).symm))).symm
  have apc109:=fun (q156 q157 q158 q159 q160:G)=>by
    exact ((cg (fun t => ((q157 ◇ q158) ◇ q158) ◇ t) (apc5 q156 q160 q159)).symm).trans (apc39 q157 q158 (q160 ◇ q156) q159 q160)
  have apc112:=fun (q161 q162:G)=>by
    exact (((apc82 q161 q162 q162).symm).trans (apc5 (q162 ◇ q161) (q162 ◇ q162) q162)).trans ((cg (fun t => q162 ◇ t) (apc93 q161 q162)).trans (apc96 (q162 ◇ q161) q162 q162))
  have apc113:=fun (q163 q164:G)=>by
    exact ((cg (fun t => (q164 ◇ q164) ◇ t) (apc5 q163 q164 q164)).symm).trans (apc112 q163 q164)
  have apc114:=fun (q165 q166 q167:G)=>by
    exact ((cg (fun t => q167 ◇ t) (apc113 q166 q165)).symm).trans (apc1 (q165 ◇ q165) q165 q166 q167)
  have apc115:=fun (q168 q169 q170:G)=>by
    exact ((cg (fun t => q170 ◇ t) (apc5 (q168 ◇ q169) q168 q168)).symm).trans (apc114 q168 q169 q170)
  have apc117:=fun (q171 q172:G)=>by
    exact ((((cg (fun t => q172 ◇ t) (cg (fun t => q171 ◇ t) (apc4 q171 q171 q171 q171))).trans (cg (fun t => q172 ◇ t) (apc96 q171 q171 q171))).symm).trans (((cg (fun t => q172 ◇ t) (cg (fun t => q171 ◇ t) (apc18 q171 q171 q171))).symm).trans (apc1 q171 (q171 ◇ q171) q171 q172))).symm
  have apc122:=fun (q173 q174 q175:G)=>by
    exact ((cg (fun t => q175 ◇ t) (cg (fun t => q173 ◇ t) (apc5 q174 q173 q173))).symm).trans (apc115 q173 q174 q175)
  have apc124:=fun (q176 q177 q178 q179 q180:G)=>by
    exact (((cg (fun t => q180 ◇ t) (cg (fun t => q178 ◇ t) (cg (fun t => q179 ◇ t) ((h q176 (q177 ◇ q179) q178).symm)))).symm).trans (apc16 (q176 ◇ (q177 ◇ q179)) q177 q178 q179 q180)).symm
  have apc125:=fun (q181 q182 q183 q184:G)=>by
    exact (((apc124 q181 q182 q183 q184 q184).symm).trans ((h (q183 ◇ q184) q184 (((q181 ◇ (q182 ◇ q184)) ◇ q182) ◇ q182)).symm)).symm
  have apc126:=fun (q185 q186 q187 q188:G)=>by
    exact (((cg (fun t => (q187 ◇ q188) ◇ t) ((h (q185 ◇ (q186 ◇ q188)) q186 q188).symm)).symm).trans (apc125 q185 q186 q187 q188)).symm
  have apc127:=fun (q189 q190 q191:G)=>by
    exact (((cg (fun t => q191 ◇ t) (cg (fun t => q191 ◇ t) (cg (fun t => q191 ◇ t) ((h q190 q191 q189).symm)))).symm).trans (apc126 q189 q190 q191 q191)).symm
  have apc128:=fun (q192 q193 q194:G)=>by
    exact ((apc127 q194 q192 q193).symm).trans ((h q194 (q192 ◇ q193) (q193 ◇ q193)).symm)
  have apc129:=fun (q195 q196:G)=>by
    exact (((apc128 q195 q195 q196).symm).trans (apc1 q195 q195 q196 q195)).symm
  have apc130:=fun (q197 q198:G)=>by
    exact ((apc129 q197 q198).symm).trans ((h (q197 ◇ q197) q197 q198).symm)
  have apc131:=fun (q195 q196 q197 q198:G)=>by
    exact (apc129 q195 q196).trans (apc130 q195 q196)
  have apc132:=fun (q199 q200:G)=>by
    exact (((cg (fun t => q200 ◇ t) (apc130 q200 q199)).symm).trans (apc96 q199 q200 q200)).symm
  have apc135:=fun (q189 q190 q191 q192 q193 q194:G)=>by
    exact (apc127 q189 q190 q191).trans (apc128 q190 q191 q189)
  have apc136:=fun (q201 q202 q203:G)=>by
    exact ((cg (fun t => q203 ◇ t) (apc1 q203 q202 q201 q203)).symm).trans (apc128 q202 q203 (q202 ◇ q201))
  have apc137:=fun (q204:G)=>by
    exact ((((cg (fun t => q204 ◇ t) (apc130 q204 q204)).trans (apc130 q204 q204)).symm).trans (((cg (fun t => q204 ◇ t) (apc132 q204 q204)).symm).trans (apc97 q204 q204 q204 q204))).symm
  have apc139:=fun (q155 q204:G)=>by
    exact (apc107 q155).trans (apc137 q155)
  have apc140:=fun (q197 q198 q143 q144:G)=>by
    exact (apc93 q143 q144).trans (apc130 q144 (q144 ◇ q143))
  have apc141:=fun (q205 q206:G)=>by
    exact (((cg (fun t => q206 ◇ t) (apc96 q206 q205 q206)).symm).trans (apc128 (q205 ◇ q206) q206 q206)).symm
  have apc144:=fun (q207 q208:G)=>by
    exact ((apc132 (q208 ◇ q207) q208).symm).trans (apc30 q207 q208 q208)
  have apc145:=fun (q209 q210 q211:G)=>by
    exact (((cg (fun t => q211 ◇ t) (apc4 q209 q211 q210 q211)).symm).trans (apc136 (q211 ◇ q209) q210 q211)).symm
  have apc146:=fun (q212 q213:G)=>by
    exact (((apc145 q212 q213 q213).symm).trans (apc130 q213 (q213 ◇ (q213 ◇ q212)))).symm
  have apc147:=fun (q214 q215:G)=>by
    exact ((((cg (fun t => q215 ◇ t) (apc20 q214 q215 q215)).symm).trans (apc136 (q214 ◇ q215) q215 q215)).trans (apc130 q215 (q215 ◇ (q214 ◇ q215)))).symm
  have apc148:=fun (q204 q171 q172:G)=>by
    exact ((apc117 q171 q172).trans (cg (fun t => q172 ◇ t) (apc137 q171))).trans (apc130 q171 q172)
  have apc149:=fun (q216:G)=>by
    exact (((apc137 q216).symm).trans (((apc148 q216 q216 (q216 ◇ q216)).symm).trans ((h (q216 ◇ (q216 ◇ q216)) (q216 ◇ q216) q216).symm))).symm
  have apc151:=fun (q217 q218:G)=>by
    exact (((apc130 q217 q218).symm).trans (((cg (fun t => q218 ◇ t) (apc149 q217)).symm).trans (apc0 q217 q217 q217 q218))).symm
  have apc155:=fun (q176 q219 q178 q179 q180:G)=>by
    exact (((cg (fun t => q180 ◇ t) (cg (fun t => q178 ◇ t) (cg (fun t => q179 ◇ t) (cg (fun t => q178 ◇ t) ((h q176 q179 q219).symm))))).symm).trans (apc16 q219 (q176 ◇ q179) q178 q179 q180)).symm
  have apc156:=fun (q220 q221 q222 q223:G)=>by
    exact (((apc155 q220 q221 q222 q223 q223).symm).trans ((h (q222 ◇ q223) q223 ((q221 ◇ (q220 ◇ q223)) ◇ (q220 ◇ q223))).symm)).symm
  have apc157:=fun (q224 q225 q226 q227:G)=>by
    exact (((cg (fun t => (q226 ◇ q227) ◇ t) ((h q225 (q224 ◇ q227) q227).symm)).symm).trans (apc156 q224 q225 q226 q227)).symm
  have apc164:=fun (q228 q229 q230:G)=>by
    exact ((cg (fun t => q230 ◇ t) (apc58 q229 q229 q228)).symm).trans (apc11 (q228 ◇ q228) q229 q229 q230)
  have apc168:=fun (q231 q232:G)=>by
    exact (((cg (fun t => q232 ◇ t) (apc4 q232 q232 q232 (q232 ◇ q231))).trans (cg (fun t => q232 ◇ t) (apc130 q232 (q232 ◇ q231)))).symm).trans ((((apc38 q231 q231 q231 q231 q231 q231 (q232 ◇ q232) q232).symm).trans (apc0 q232 q232 q232 ((q232 ◇ q231) ◇ q231))).trans ((apc151 q232 ((q232 ◇ q231) ◇ q231)).trans (apc21 ((q232 ◇ q232) ◇ (q232 ◇ ((q232 ◇ q231) ◇ q231))) ((q232 ◇ q232) ◇ (q232 ◇ ((q232 ◇ q231) ◇ q231))) ((q232 ◇ q232) ◇ (q232 ◇ ((q232 ◇ q231) ◇ q231))) q231 q232 q232)))
  have apc169:=fun (q207 q208 q231 q232:G)=>by
    exact (((apc168 q207 q208).symm).trans (apc144 q207 q208)).symm
  have apc170:=fun (q231 q232 q168 q169 q170:G)=>by
    exact (((cg (fun t => q170 ◇ t) (apc168 q169 q168)).symm).trans (apc115 q168 q169 q170)).symm
  have apc171:=fun (q233 q234:G)=>by
    exact ((apc170 q233 q233 q233 q234 q233).symm).trans ((h ((q233 ◇ q233) ◇ q233) q233 q234).symm)
  have apc172:=fun (q233 q234 q214 q215:G)=>by
    exact (apc147 q214 q215).trans (apc171 q215 q214)
  have apc173:=fun (q207 q208 q212 q213 q231 q232:G)=>by
    exact (apc146 q212 q213).trans (apc169 q212 q213 (q213 ◇ (q213 ◇ ((q213 ◇ q213) ◇ (q213 ◇ q212)))) (q213 ◇ (q213 ◇ ((q213 ◇ q213) ◇ (q213 ◇ q212)))))
  have apc178:=fun (q235 q236:G)=>by
    exact (((cg (fun t => q236 ◇ t) (cg (fun t => (q236 ◇ q236) ◇ t) ((h q235 q236 q236).symm))).symm).trans (apc171 q236 (q235 ◇ q236))).symm
  have apc179:=fun (q237 q238:G)=>by
    exact (((apc171 q238 q237).symm).trans (((cg (fun t => q238 ◇ t) (apc168 q237 q238)).symm).trans (apc169 (q238 ◇ q237) q238 q237 q237))).symm
  have apc182:=fun (q239 q240:G)=>by
    exact ((apc171 q239 q240).symm).trans ((((cg (fun t => q239 ◇ t) (apc169 q240 q239 q239 q239)).symm).trans (apc128 (q239 ◇ q239) q239 q240)).trans ((cg (fun t => q240 ◇ t) (apc139 q239 (((q239 ◇ q239) ◇ q239) ◇ (q239 ◇ q239)))).trans (apc130 q239 q240)))
  have apc183:=fun (q239 q240 q233 q234:G)=>by
    exact (apc171 q233 q234).trans (apc182 q233 q234)
  have apc184:=fun (q239 q240 q233 q234 q214 q215:G)=>by
    exact (apc172 q214 q214 q214 q215).trans (apc182 q215 q214)
  have apc185:=fun (q237 q238 q239 q240:G)=>by
    exact (apc179 q237 q238).trans (apc182 q238 q237)
  have apc186:=fun (q235 q236 q239 q240:G)=>by
    exact (((apc182 q236 (q235 ◇ q236)).symm).trans (apc178 q235 q236)).symm
  have apc188:=fun (q241 q242:G)=>by
    exact (((cg (fun t => q242 ◇ t) (apc184 q241 q241 q241 q241 q241 q242)).symm).trans (apc168 (q241 ◇ q242) q242)).symm
  have apc189:=fun (q243 q244:G)=>by
    exact ((cg (fun t => (q244 ◇ q244) ◇ t) ((h q243 q244 q244).symm)).symm).trans (apc188 q243 q244)
  have apc192:=fun (q245 q246:G)=>by
    exact (((apc53 q245 (q245 ◇ q245) q246).symm).trans (apc1 (q245 ◇ q245) q245 (q245 ◇ q245) q246)).trans (((apc43 q245 q245 q246).trans (cg (fun t => q246 ◇ t) (apc149 q245))).trans (apc130 q245 q246))
  have apc202:=fun (q247 q248 q249 q250 q251:G)=>by
    exact ((cg (fun t => ((q251 ◇ q249) ◇ q249) ◇ t) ((h q247 q248 ((q250 ◇ q251) ◇ q251)).symm)).symm).trans (apc17 q249 q250 q251 ((q247 ◇ q248) ◇ q248))
  have apc204:=fun (q252 q253 q254 q255 q256:G)=>by
    exact (((cg (fun t => ((q256 ◇ q254) ◇ q254) ◇ t) (cg (fun t => q252 ◇ t) ((h q255 q256 q253).symm))).symm).trans (apc202 q252 q253 q254 q255 q256)).symm
  have apc205:=fun (q257 q258 q259 q260 q261:G)=>by
    exact ((cg (fun t => (q259 ◇ q261) ◇ t) ((h q257 q258 ((q260 ◇ q261) ◇ q261)).symm)).symm).trans (apc204 q257 q258 q259 q260 q261)
  have apc206:=fun (q262 q263 q264 q265 q266:G)=>by
    exact (((cg (fun t => (q264 ◇ q266) ◇ t) (cg (fun t => q262 ◇ t) ((h q265 q266 q263).symm))).symm).trans (apc205 q262 q263 q264 q265 q266)).symm
  have apc225:=fun (q267 q268 q269:G)=>by
    exact ((cg (fun t => (q269 ◇ q268) ◇ t) (apc182 q269 q267)).symm).trans (apc4 q268 q269 q269 (q269 ◇ q267))
  have apc227:=fun (q270 q271:G)=>by
    exact (((apc109 q270 q271 q271 q271 q271).symm).trans (apc5 (q271 ◇ q270) (q271 ◇ q271) q271)).trans ((cg (fun t => q271 ◇ t) (apc140 ((q271 ◇ (q271 ◇ q271)) ◇ ((q271 ◇ q271) ◇ (q271 ◇ q270))) ((q271 ◇ (q271 ◇ q271)) ◇ ((q271 ◇ q271) ◇ (q271 ◇ q270))) q270 q271)).trans (apc168 q270 q271))
  have apc228:=fun (q272 q273:G)=>by
    exact (((((cg (fun t => q273 ◇ t) (apc185 (q272 ◇ q272) q272 ((q272 ◇ q272) ◇ (q272 ◇ ((q272 ◇ (q272 ◇ q272)) ◇ q272))) ((q272 ◇ q272) ◇ (q272 ◇ ((q272 ◇ (q272 ◇ q272)) ◇ q272))))).trans (cg (fun t => q273 ◇ t) (apc137 q272))).trans (apc130 q272 q273)).symm).trans (((cg (fun t => q273 ◇ t) (apc227 (q272 ◇ (q272 ◇ q272)) q272)).symm).trans ((h q272 (q272 ◇ (q272 ◇ (q272 ◇ q272))) q273).symm))).symm
  have apc229:=fun (q274:G)=>by
    exact (((((apc58 q274 q274 q274).trans (apc130 q274 (q274 ◇ q274))).trans (apc137 q274)).symm).trans (((apc228 q274 (q274 ◇ (q274 ◇ q274))).symm).trans ((h q274 (q274 ◇ (q274 ◇ q274)) q274).symm))).symm
  have apc230:=fun (q275 q276 q277:G)=>by
    exact ((cg (fun t => q277 ◇ t) ((h q275 q276 (q277 ◇ (q277 ◇ (q277 ◇ q277)))).symm)).symm).trans (apc228 q277 ((q275 ◇ q276) ◇ q276))
  have apc239:=fun (q278 q279 q280 q281:G)=>by
    exact (((cg (fun t => q281 ◇ t) (cg (fun t => q280 ◇ t) (cg (fun t => q281 ◇ t) ((h q278 (q281 ◇ q279) q280).symm)))).symm).trans (apc157 (q278 ◇ (q281 ◇ q279)) q279 q280 q281)).symm
  have apc240:=fun (q282 q283 q284 q285:G)=>by
    exact (((cg (fun t => (q284 ◇ q285) ◇ t) ((h (q282 ◇ (q285 ◇ q283)) q285 q283).symm)).symm).trans (apc239 q282 q283 q284 q285)).symm
  have apc241:=fun (q286 q287 q288:G)=>by
    exact (((cg (fun t => q288 ◇ t) (cg (fun t => q287 ◇ t) (cg (fun t => q288 ◇ t) ((h q288 q287 q286).symm)))).symm).trans (apc240 q286 q287 q287 q288)).symm
  have apc242:=fun (q289 q290 q291:G)=>by
    exact ((apc241 q291 q289 q290).symm).trans ((h q291 (q290 ◇ q289) (q289 ◇ q290)).symm)
  have apc244:=fun (q292 q293 q294:G)=>by
    exact (((cg (fun t => (q294 ◇ q294) ◇ t) (cg (fun t => q294 ◇ t) ((h q292 q293 q294).symm))).symm).trans (apc132 ((q292 ◇ q293) ◇ q293) q294)).trans (apc36 (q294 ◇ ((q294 ◇ q294) ◇ (q294 ◇ ((q292 ◇ q293) ◇ q293)))) (q294 ◇ ((q294 ◇ q294) ◇ (q294 ◇ ((q292 ◇ q293) ◇ q293)))) (q294 ◇ ((q294 ◇ q294) ◇ (q294 ◇ ((q292 ◇ q293) ◇ q293)))) (q294 ◇ ((q294 ◇ q294) ◇ (q294 ◇ ((q292 ◇ q293) ◇ q293)))) (q294 ◇ ((q294 ◇ q294) ◇ (q294 ◇ ((q292 ◇ q293) ◇ q293)))) q292 q293 q294 q294 q294)
  have apc245:=fun (q295 q296:G)=>by
    exact ((((cg (fun t => q296 ◇ t) (apc186 q295 q296 (q296 ◇ ((q296 ◇ q296) ◇ (q295 ◇ (q296 ◇ q296)))) (q296 ◇ ((q296 ◇ q296) ◇ (q295 ◇ (q296 ◇ q296)))))).trans (apc183 (q296 ◇ ((q296 ◇ q296) ◇ (q296 ◇ (q295 ◇ q296)))) (q296 ◇ ((q296 ◇ q296) ◇ (q296 ◇ (q295 ◇ q296)))) q296 q295)).symm).trans (((cg (fun t => q296 ◇ t) (apc141 q295 q296)).symm).trans (apc96 q296 (q295 ◇ q296) q296))).symm
  have apc250:=fun (q297 q298 q299 q300:G)=>by
    exact (((cg (fun t => (q299 ◇ q300) ◇ t) ((h q297 (q299 ◇ q298) q300).symm)).symm).trans (apc49 (q297 ◇ (q299 ◇ q298)) q298 q299 q300)).symm
  have apc252:=fun (q301 q302 q303 q304:G)=>by
    exact (((cg (fun t => q304 ◇ t) ((h q301 (q303 ◇ q302) (q304 ◇ q303)).symm)).symm).trans (apc250 q301 q302 q303 q304)).symm
  have apc255:=fun (q305:G)=>by
    exact ((((apc130 q305 (q305 ◇ q305)).trans (apc137 q305)).symm).trans (((cg (fun t => (q305 ◇ q305) ◇ t) (apc229 q305)).symm).trans (apc252 q305 (q305 ◇ q305) q305 q305))).symm
  have apc256:=fun (q306:G)=>by
    exact ((cg (fun t => q306 ◇ t) ((h q306 (q306 ◇ q306) q306).symm)).symm).trans (apc255 q306)
  have apc257:=fun (q307:G)=>by
    exact (((cg (fun t => q307 ◇ t) ((h q307 q307 q307).symm)).symm).trans (apc256 q307)).symm
  have apc260:=fun (q308 q309:G)=>by
    exact ((cg (fun t => q309 ◇ t) (apc257 q308)).symm).trans (apc130 q308 q309)
  have apc264:=fun (q310 q311 q312:G)=>by
    exact ((((cg (fun t => q312 ◇ t) (cg (fun t => q310 ◇ t) (apc182 q311 q311))).trans (cg (fun t => q312 ◇ t) (apc130 q311 q310))).symm).trans (((cg (fun t => q312 ◇ t) (apc1 q311 q311 q310 (q311 ◇ q311))).symm).trans (apc114 q311 (q311 ◇ q310) q312))).symm
  have apc268:=fun (q313 q314 q315:G)=>by
    exact (((cg (fun t => ((q315 ◇ q315) ◇ q315) ◇ t) ((h q313 q314 q315).symm)).symm).trans (apc182 q315 ((q313 ◇ q314) ◇ q314))).symm
  have apc269:=fun (q316 q317 q318:G)=>by
    exact (((cg (fun t => (q318 ◇ q318) ◇ t) ((h q316 q317 q318).symm)).symm).trans (apc268 q316 q317 q318)).symm
  have apc270:=fun (q313 q314 q315 q316 q317 q318:G)=>by
    exact (apc268 q313 q314 q315).trans (apc269 q313 q314 q315)
  have apc280:=fun (q319 q320 q321 q322:G)=>by
    exact ((apc55 (q322 ◇ (q320 ◇ (q321 ◇ q319))) q319 q320 q321).symm).trans ((h q322 (q320 ◇ (q321 ◇ q319)) ((q321 ◇ q320) ◇ q320)).symm)
  have apc281:=fun (q323 q324 q325 q326:G)=>by
    exact ((apc280 q323 q324 q325 q326).symm).trans ((h q326 (q324 ◇ (q325 ◇ q323)) (q324 ◇ q325)).symm)
  have apc283:=fun (q327 q328 q329 q330:G)=>by
    exact (((cg (fun t => q330 ◇ t) ((h q329 q328 (q328 ◇ (q329 ◇ q327))).symm)).symm).trans (apc281 q327 q328 q329 q330)).symm
  have apc284:=fun (q331 q332:G)=>by
    exact (((cg (fun t => q332 ◇ t) (apc260 q331 q331)).trans (apc130 q331 q332)).symm).trans (((apc283 q331 q331 q331 q332).symm).trans ((h q331 (q331 ◇ q331) q332).symm))
  have apc314:=fun (q333:G)=>by
    exact ((apc284 q333 q333).symm).trans (apc257 q333)
  have apc315:=fun (q334:G)=>by
    exact ((apc314 q334).symm).trans ((h q334 q334 q334).symm)
  have apc317:=fun (q307 q334:G)=>by
    exact (apc257 q307).trans (apc315 q307)
  have apc320:=fun (q307 q204 q334:G)=>by
    exact (apc137 q204).trans (apc317 q204 ((q204 ◇ q204) ◇ (q204 ◇ q204)))
  have apc382:=fun (q333 q334:G)=>by
    exact (apc314 q333).trans (apc315 q333)
  have apc388:=fun (q308 q309 q334:G)=>by
    exact ((cg (fun t => q309 ◇ t) (apc315 q308)).symm).trans (apc260 q308 q309)
  have apc395:=fun (q272 q273 q334:G)=>by
    exact ((cg (fun t => q272 ◇ t) (cg (fun t => t ◇ q273) (apc315 q272))).symm).trans (apc228 q272 q273)
  have apc421:=fun (q335 q336:G)=>by
    exact ((cg (fun t => t ◇ ((q335 ◇ q335) ◇ q336)) (apc382 q335 (q335 ◇ ((q335 ◇ q335) ◇ q335)))).symm).trans ((((cg (fun t => t ◇ ((q335 ◇ q335) ◇ q336)) (apc284 q335 q335)).symm).trans (apc284 (q335 ◇ q335) q336)).trans (cg (fun t => (q335 ◇ q335) ◇ t) (cg (fun t => t ◇ q336) (apc317 q335 ((q335 ◇ q335) ◇ (q335 ◇ q335))))))
  have apc428:=fun (q337 q338 q339:G)=>by
    exact ((apc39 q338 q339 q337 q338 q338).symm).trans ((((cg (fun t => ((q338 ◇ q339) ◇ q339) ◇ t) (apc130 q338 q337)).symm).trans (apc206 q337 q338 q339 (q338 ◇ q338) q338)).trans ((cg (fun t => (q339 ◇ q338) ◇ t) (cg (fun t => q337 ◇ t) (apc317 q338 ((q338 ◇ q338) ◇ (q338 ◇ q338))))).trans (cg (fun t => (q339 ◇ q338) ◇ t) (apc388 q338 q337 (q337 ◇ (q338 ◇ (q338 ◇ q338)))))))
  have apc429:=fun (q337 q338 q339 q207 q208 q212 q213 q231 q232:G)=>by
    exact (((cg (fun t => (q212 ◇ q213) ◇ t) (apc317 q213 ((q213 ◇ q213) ◇ (q213 ◇ q213)))).symm).trans (((apc428 q213 q213 q212).symm).trans (apc173 q212 q212 q212 q213 q212 q212))).symm
  have apc430:=fun (q337 q338 q339 q207 q208 q212 q213 q237 q238 q239 q240 q231 q232:G)=>by
    exact ((apc429 ((q238 ◇ q238) ◇ (q238 ◇ ((q238 ◇ q237) ◇ q238))) ((q238 ◇ q238) ◇ (q238 ◇ ((q238 ◇ q237) ◇ q238))) ((q238 ◇ q238) ◇ (q238 ◇ ((q238 ◇ q237) ◇ q238))) ((q238 ◇ q238) ◇ (q238 ◇ ((q238 ◇ q237) ◇ q238))) ((q238 ◇ q238) ◇ (q238 ◇ ((q238 ◇ q237) ◇ q238))) (q238 ◇ q237) q238 ((q238 ◇ q238) ◇ (q238 ◇ ((q238 ◇ q237) ◇ q238))) ((q238 ◇ q238) ◇ (q238 ◇ ((q238 ◇ q237) ◇ q238)))).symm).trans (apc185 q237 q238 q237 q237)
  have apc433:=fun (q235 q236 q337 q338 q339 q207 q208 q212 q213 q239 q240 q231 q232:G)=>by
    exact (apc186 q235 q236 q235 q235).trans (apc429 ((q236 ◇ q236) ◇ (q236 ◇ (q235 ◇ q236))) ((q236 ◇ q236) ◇ (q236 ◇ (q235 ◇ q236))) ((q236 ◇ q236) ◇ (q236 ◇ (q235 ◇ q236))) ((q236 ◇ q236) ◇ (q236 ◇ (q235 ◇ q236))) ((q236 ◇ q236) ◇ (q236 ◇ (q235 ◇ q236))) q235 q236 ((q236 ◇ q236) ◇ (q236 ◇ (q235 ◇ q236))) ((q236 ◇ q236) ◇ (q236 ◇ (q235 ◇ q236))))
  have apc442:=fun (q340 q341:G)=>by
    exact (((cg (fun t => q341 ◇ t) (cg (fun t => t ◇ (q340 ◇ q340)) (apc388 q340 q340 (q340 ◇ (q340 ◇ (q340 ◇ q340)))))).trans (cg (fun t => q341 ◇ t) (cg (fun t => t ◇ (q340 ◇ q340)) (apc317 q340 ((q340 ◇ q340) ◇ (q340 ◇ q340)))))).symm).trans (((cg (fun t => q341 ◇ t) (cg (fun t => t ◇ (q340 ◇ q340)) (apc257 q340))).symm).trans ((h (q340 ◇ q340) (q340 ◇ q340) q341).symm))
  have apc457:=fun (q342 q343 q344:G)=>by
    exact (((cg (fun t => q344 ◇ t) (cg (fun t => q342 ◇ t) (cg (fun t => q343 ◇ t) (cg (fun t => t ◇ (q344 ◇ q344)) (apc317 q344 ((q344 ◇ q344) ◇ (q344 ◇ q344))))))).trans (cg (fun t => q344 ◇ t) (cg (fun t => q342 ◇ t) (apc442 q344 q343)))).symm).trans ((((cg (fun t => q344 ◇ t) ((h q342 q343 (((q344 ◇ q344) ◇ (q344 ◇ q344)) ◇ (q344 ◇ q344))).symm)).symm).trans (apc192 q344 ((q342 ◇ q343) ◇ q343))).trans (apc270 q342 q343 q344 ((q344 ◇ q344) ◇ (q344 ◇ ((q342 ◇ q343) ◇ q343))) ((q344 ◇ q344) ◇ (q344 ◇ ((q342 ◇ q343) ◇ q343))) ((q344 ◇ q344) ◇ (q344 ◇ ((q342 ◇ q343) ◇ q343)))))
  have apc465:=fun (q345 q346:G)=>by
    exact ((apc53 q345 q346 q345).symm).trans ((((cg (fun t => q345 ◇ t) (cg (fun t => q346 ◇ t) (cg (fun t => q345 ◇ t) (apc130 q345 q346)))).symm).trans (apc157 (q345 ◇ q345) q345 q346 q345)).trans (((cg (fun t => (q346 ◇ q345) ◇ t) (apc131 q345 q345 (q345 ◇ (((q345 ◇ q345) ◇ q345) ◇ q345)) (q345 ◇ (((q345 ◇ q345) ◇ q345) ◇ q345)))).trans (cg (fun t => (q346 ◇ q345) ◇ t) (apc317 q345 ((q345 ◇ q345) ◇ (q345 ◇ q345))))).trans (apc388 q345 (q346 ◇ q345) ((q346 ◇ q345) ◇ (q345 ◇ (q345 ◇ q345))))))
  have apc469:=fun (q347 q348:G)=>by
    exact ((apc270 q347 q348 q348 ((q348 ◇ q348) ◇ (q348 ◇ ((q347 ◇ q348) ◇ q348))) ((q348 ◇ q348) ◇ (q348 ◇ ((q347 ◇ q348) ◇ q348))) ((q348 ◇ q348) ◇ (q348 ◇ ((q347 ◇ q348) ◇ q348)))).symm).trans ((((apc186 (q347 ◇ q348) q348 q347 q347).symm).trans (apc96 (q348 ◇ q348) q347 q348)).trans (((cg (fun t => (q348 ◇ q348) ◇ t) (apc388 q348 q347 (q347 ◇ (q348 ◇ (q348 ◇ q348))))).trans (apc225 q347 q348 q348)).trans (cg (fun t => (q348 ◇ q347) ◇ t) (apc317 q348 ((q348 ◇ q348) ◇ (q348 ◇ q348))))))
  have apc470:=fun (q295 q296 q347 q348:G)=>by
    exact ((apc469 (q295 ◇ q296) q296).symm).trans (apc245 q295 q296)
  have apc471:=fun (q243 q244 q347 q348:G)=>by
    exact ((apc469 q243 q244).symm).trans (apc189 q243 q244)
  have apc472:=fun (q235 q236 q337 q338 q339 q207 q208 q212 q213 q239 q240 q347 q348 q231 q232:G)=>by
    exact ((cg (fun t => q236 ◇ t) (apc469 q235 q236)).symm).trans (apc433 q235 q236 q235 q235 q235 q235 q235 q235 q235 q235 q235 q235 q235)
  have apc473:=fun (q275 q276 q277 q308 q309:G)=>by
    exact (((cg (fun t => q277 ◇ t) (cg (fun t => q275 ◇ t) (apc260 q277 q276))).symm).trans (apc230 q275 q276 q277)).trans (apc270 q275 q276 q277 ((q277 ◇ q277) ◇ (q277 ◇ ((q275 ◇ q276) ◇ q276))) ((q277 ◇ q277) ◇ (q277 ◇ ((q275 ◇ q276) ◇ q276))) ((q277 ◇ q277) ◇ (q277 ◇ ((q275 ◇ q276) ◇ q276))))
  have apc533:=fun (q349 q350:G)=>by
    exact (((cg (fun t => q350 ◇ t) (apc473 q350 q349 q350 (q350 ◇ (q350 ◇ ((q350 ◇ q350) ◇ (q350 ◇ q349)))) (q350 ◇ (q350 ◇ ((q350 ◇ q350) ◇ (q350 ◇ q349)))))).trans (cg (fun t => q350 ◇ t) (apc429 ((q350 ◇ q350) ◇ (q350 ◇ (q349 ◇ q350))) ((q350 ◇ q350) ◇ (q350 ◇ (q349 ◇ q350))) ((q350 ◇ q350) ◇ (q350 ◇ (q349 ◇ q350))) ((q350 ◇ q350) ◇ (q350 ◇ (q349 ◇ q350))) ((q350 ◇ q350) ◇ (q350 ◇ (q349 ◇ q350))) q349 q350 ((q350 ◇ q350) ◇ (q350 ◇ (q349 ◇ q350))) ((q350 ◇ q350) ◇ (q350 ◇ (q349 ◇ q350)))))).symm).trans ((((cg (fun t => q350 ◇ t) (cg (fun t => q350 ◇ t) (apc5 q349 q350 q350))).symm).trans (apc169 (q350 ◇ q349) q350 q349 q349)).trans ((apc429 ((q350 ◇ q350) ◇ (q350 ◇ ((q350 ◇ q349) ◇ q350))) ((q350 ◇ q350) ◇ (q350 ◇ ((q350 ◇ q349) ◇ q350))) ((q350 ◇ q350) ◇ (q350 ◇ ((q350 ◇ q349) ◇ q350))) ((q350 ◇ q350) ◇ (q350 ◇ ((q350 ◇ q349) ◇ q350))) ((q350 ◇ q350) ◇ (q350 ◇ ((q350 ◇ q349) ◇ q350))) (q350 ◇ q349) q350 ((q350 ◇ q350) ◇ (q350 ◇ ((q350 ◇ q349) ◇ q350))) ((q350 ◇ q350) ◇ (q350 ◇ ((q350 ◇ q349) ◇ q350)))).trans (apc430 (((q350 ◇ q349) ◇ q350) ◇ (q350 ◇ (q350 ◇ q350))) (((q350 ◇ q349) ◇ q350) ◇ (q350 ◇ (q350 ◇ q350))) (((q350 ◇ q349) ◇ q350) ◇ (q350 ◇ (q350 ◇ q350))) (((q350 ◇ q349) ◇ q350) ◇ (q350 ◇ (q350 ◇ q350))) (((q350 ◇ q349) ◇ q350) ◇ (q350 ◇ (q350 ◇ q350))) (((q350 ◇ q349) ◇ q350) ◇ (q350 ◇ (q350 ◇ q350))) (((q350 ◇ q349) ◇ q350) ◇ (q350 ◇ (q350 ◇ q350))) q349 q350 (((q350 ◇ q349) ◇ q350) ◇ (q350 ◇ (q350 ◇ q350))) (((q350 ◇ q349) ◇ q350) ◇ (q350 ◇ (q350 ◇ q350))) (((q350 ◇ q349) ◇ q350) ◇ (q350 ◇ (q350 ◇ q350))) (((q350 ◇ q349) ◇ q350) ◇ (q350 ◇ (q350 ◇ q350))))))
  have apc544:=fun (q351 q352 q353:G)=>by
    exact ((((cg (fun t => q353 ◇ t) (cg (fun t => q351 ◇ t) (apc442 q353 q352))).trans (apc457 q351 q352 q353)).symm).trans ((((cg (fun t => q353 ◇ t) ((h q351 q352 ((q353 ◇ (q353 ◇ q353)) ◇ (q353 ◇ q353))).symm)).symm).trans (apc117 q353 ((q351 ◇ q352) ◇ q352))).trans (cg (fun t => ((q351 ◇ q352) ◇ q352) ◇ t) (apc320 ((q353 ◇ q353) ◇ (q353 ◇ (q353 ◇ q353))) q353 ((q353 ◇ q353) ◇ (q353 ◇ (q353 ◇ q353))))))).symm
  have apc559:=fun (q354 q355 q356:G)=>by
    exact ((cg (fun t => q356 ◇ t) (cg (fun t => ((q354 ◇ q354) ◇ (q354 ◇ q355)) ◇ t) (apc317 q354 ((q354 ◇ q354) ◇ (q354 ◇ q354))))).symm).trans ((((cg (fun t => q356 ◇ t) (apc129 q354 ((q354 ◇ q354) ◇ (q354 ◇ q355)))).symm).trans (apc0 (q354 ◇ q354) q354 q355 q356)).trans (apc170 (q355 ◇ ((((q354 ◇ q354) ◇ q354) ◇ q354) ◇ q356)) (q355 ◇ ((((q354 ◇ q354) ◇ q354) ◇ q354) ◇ q356)) q354 q355 q356))
  have apc563:=fun (q357 q358 q359:G)=>by
    exact ((((cg (fun t => (q357 ◇ (q358 ◇ q359)) ◇ t) (apc131 q359 q359 (q359 ◇ (((q359 ◇ q359) ◇ q359) ◇ q359)) (q359 ◇ (((q359 ◇ q359) ◇ q359) ◇ q359)))).trans (cg (fun t => (q357 ◇ (q358 ◇ q359)) ◇ t) (apc317 q359 ((q359 ◇ q359) ◇ (q359 ◇ q359))))).symm).trans (((cg (fun t => (q357 ◇ (q358 ◇ q359)) ◇ t) (apc14 q359)).symm).trans (apc35 q357 q358 q359 q359 (q359 ◇ (q359 ◇ q359))))).symm
  have apc572:=fun (q360 q361:G)=>by
    exact ((((((cg (fun t => q361 ◇ t) (cg (fun t => t ◇ (q360 ◇ (q360 ◇ q360))) (apc317 q360 ((q360 ◇ q360) ◇ (q360 ◇ q360))))).trans (cg (fun t => q361 ◇ t) (apc470 q360 q360 ((q360 ◇ (q360 ◇ q360)) ◇ (q360 ◇ (q360 ◇ q360))) ((q360 ◇ (q360 ◇ q360)) ◇ (q360 ◇ (q360 ◇ q360)))))).trans (cg (fun t => q361 ◇ t) (apc317 q360 ((q360 ◇ q360) ◇ (q360 ◇ q360))))).trans (apc388 q360 q361 (q361 ◇ (q360 ◇ (q360 ◇ q360))))).symm).trans (((cg (fun t => q361 ◇ t) (cg (fun t => t ◇ (q360 ◇ (q360 ◇ q360))) (apc137 q360))).symm).trans ((h (q360 ◇ q360) (q360 ◇ (q360 ◇ q360)) q361).symm))).symm
  have apc573:=fun (q360 q361 q335 q336:G)=>by
    exact (apc421 q335 q336).trans (apc572 q335 q336)
  have apc574:=fun (q360 q361 q357 q358 q359 q335 q336:G)=>by
    exact ((apc573 ((q359 ◇ (q359 ◇ q359)) ◇ ((q359 ◇ q359) ◇ (q357 ◇ (q358 ◇ q359)))) ((q359 ◇ (q359 ◇ q359)) ◇ ((q359 ◇ q359) ◇ (q357 ◇ (q358 ◇ q359)))) q359 (q357 ◇ (q358 ◇ q359))).symm).trans (apc563 q357 q358 q359)
  have apc577:=fun (q292 q293 q294 q360 q361 q357 q358 q359 q335 q336:G)=>by
    exact ((apc574 ((q294 ◇ q294) ◇ (q294 ◇ (q292 ◇ (q293 ◇ q294)))) ((q294 ◇ q294) ◇ (q294 ◇ (q292 ◇ (q293 ◇ q294)))) q292 q293 q294 ((q294 ◇ q294) ◇ (q294 ◇ (q292 ◇ (q293 ◇ q294)))) ((q294 ◇ q294) ◇ (q294 ◇ (q292 ◇ (q293 ◇ q294))))).symm).trans (apc244 q292 q293 q294)
  have apc589:=fun (q362 q363 q364:G)=>by
    exact (((cg (fun t => q364 ◇ t) (cg (fun t => ((q362 ◇ q362) ◇ (q362 ◇ q363)) ◇ t) (apc317 q362 ((q362 ◇ q362) ◇ (q362 ◇ q362))))).trans (apc559 q362 q363 q364)).symm).trans ((((cg (fun t => q364 ◇ t) (cg (fun t => t ◇ ((q362 ◇ q362) ◇ (q362 ◇ q362))) (apc130 q362 q363))).symm).trans ((h q363 ((q362 ◇ q362) ◇ (q362 ◇ q362)) q364).symm)).trans (cg (fun t => q363 ◇ t) (cg (fun t => t ◇ q364) (apc317 q362 ((q362 ◇ q362) ◇ (q362 ◇ q362))))))
  have apc590:=fun (q362 q363 q364 q239 q240 q233 q234:G)=>by
    exact ((apc589 q233 q234 q233).symm).trans (apc183 q233 q233 q233 q234)
  have apc593:=fun (q362 q363 q364 q231 q232 q168 q169 q170:G)=>by
    exact (apc170 q168 q168 q168 q169 q170).trans (apc589 q168 q169 q170)
  have apc594:=fun (q362 q363 q364 q310 q311 q312 q231 q232 q168 q169 q170:G)=>by
    exact ((apc593 ((q311 ◇ q310) ◇ ((((q311 ◇ q311) ◇ q311) ◇ q311) ◇ q312)) ((q311 ◇ q310) ◇ ((((q311 ◇ q311) ◇ q311) ◇ q311) ◇ q312)) ((q311 ◇ q310) ◇ ((((q311 ◇ q311) ◇ q311) ◇ q311) ◇ q312)) ((q311 ◇ q310) ◇ ((((q311 ◇ q311) ◇ q311) ◇ q311) ◇ q312)) ((q311 ◇ q310) ◇ ((((q311 ◇ q311) ◇ q311) ◇ q311) ◇ q312)) q311 (q311 ◇ q310) q312).symm).trans (apc264 q310 q311 q312)
  have apc607:=fun (q365 q366 q367:G)=>by
    exact (((cg (fun t => q367 ◇ t) (cg (fun t => q366 ◇ t) (cg (fun t => (q365 ◇ q367) ◇ t) (apc388 q367 q367 (q367 ◇ (q367 ◇ (q367 ◇ q367))))))).trans (cg (fun t => q367 ◇ t) (cg (fun t => q366 ◇ t) (cg (fun t => (q365 ◇ q367) ◇ t) (apc317 q367 ((q367 ◇ q367) ◇ (q367 ◇ q367))))))).symm).trans (((cg (fun t => q367 ◇ t) (apc4 (q367 ◇ (q367 ◇ q367)) q367 q365 q366)).symm).trans (apc228 q367 (((q367 ◇ q365) ◇ q365) ◇ q366)))
  have apc646:=fun (q368 q369 q370 q371:G)=>by
    exact ((apc593 ((q368 ◇ (q369 ◇ q370)) ◇ ((((q370 ◇ q370) ◇ q370) ◇ q370) ◇ q371)) ((q368 ◇ (q369 ◇ q370)) ◇ ((((q370 ◇ q370) ◇ q370) ◇ q370) ◇ q371)) ((q368 ◇ (q369 ◇ q370)) ◇ ((((q370 ◇ q370) ◇ q370) ◇ q370) ◇ q371)) ((q368 ◇ (q369 ◇ q370)) ◇ ((((q370 ◇ q370) ◇ q370) ◇ q370) ◇ q371)) ((q368 ◇ (q369 ◇ q370)) ◇ ((((q370 ◇ q370) ◇ q370) ◇ q370) ◇ q371)) q370 (q368 ◇ (q369 ◇ q370)) q371).symm).trans ((((cg (fun t => t ◇ ((((q370 ◇ q370) ◇ q370) ◇ q370) ◇ q371)) ((h q368 q369 q370).symm)).symm).trans (apc264 ((q368 ◇ q369) ◇ q369) q370 q371)).trans (cg (fun t => q371 ◇ t) (apc270 q368 q369 q370 ((q370 ◇ q370) ◇ (q370 ◇ ((q368 ◇ q369) ◇ q369))) ((q370 ◇ q370) ◇ (q370 ◇ ((q368 ◇ q369) ◇ q369))) ((q370 ◇ q370) ◇ (q370 ◇ ((q368 ◇ q369) ◇ q369))))))
  have apc654:=fun (q372 q373 q374 q375 q376 q377:G)=>by
    exact ((cg (fun t => (q374 ◇ (q376 ◇ q375)) ◇ t) ((h q372 q373 ((q376 ◇ q377) ◇ q377)).symm)).symm).trans (apc75 q374 q375 q376 q377 ((q372 ◇ q373) ◇ q373))
  have apc655:=fun (q378 q379 q380:G)=>by
    exact ((((cg (fun t => (q378 ◇ (q380 ◇ q379)) ◇ t) (apc131 q380 q380 (q380 ◇ (((q380 ◇ q380) ◇ q380) ◇ q380)) (q380 ◇ (((q380 ◇ q380) ◇ q380) ◇ q380)))).trans (cg (fun t => (q378 ◇ (q380 ◇ q379)) ◇ t) (apc317 q380 ((q380 ◇ q380) ◇ (q380 ◇ q380))))).symm).trans ((((cg (fun t => (q378 ◇ (q380 ◇ q379)) ◇ t) (apc14 q380)).symm).trans (apc75 q378 q379 q380 q380 (q380 ◇ (q380 ◇ q380)))).trans (apc573 ((q380 ◇ (q380 ◇ q380)) ◇ ((q380 ◇ q380) ◇ (q378 ◇ (q380 ◇ q379)))) ((q380 ◇ (q380 ◇ q380)) ◇ ((q380 ◇ q380) ◇ (q378 ◇ (q380 ◇ q379)))) q380 (q378 ◇ (q380 ◇ q379))))).symm
  have apc662:=fun (q381 q382 q383 q384 q385:G)=>by
    exact ((((cg (fun t => (((q381 ◇ q383) ◇ q384) ◇ q384) ◇ t) (cg (fun t => q382 ◇ t) ((h q381 q383 q385).symm))).symm).trans (apc206 q382 q383 q384 q385 (q381 ◇ q383))).trans (apc654 q382 q385 q384 q383 q381 q383)).symm
  have apc678:=fun (q386 q387:G)=>by
    exact ((apc1 q386 (q386 ◇ q386) q387 q386).symm).trans ((((cg (fun t => q386 ◇ t) (apc5 ((q386 ◇ q386) ◇ q387) q386 q386)).symm).trans (apc242 (q386 ◇ q386) q386 q387)).trans (((cg (fun t => q387 ◇ t) (apc573 ((q386 ◇ (q386 ◇ q386)) ◇ ((q386 ◇ q386) ◇ q386)) ((q386 ◇ (q386 ◇ q386)) ◇ ((q386 ◇ q386) ◇ q386)) q386 q386)).trans (cg (fun t => q387 ◇ t) (apc317 q386 ((q386 ◇ q386) ◇ (q386 ◇ q386))))).trans (apc388 q386 q387 (q387 ◇ (q386 ◇ (q386 ◇ q386))))))
  have apc696:=fun (q388 q389:G)=>by
    exact (((cg (fun t => q389 ◇ t) (apc678 q389 q388)).symm).trans ((((cg (fun t => q389 ◇ t) (apc1 q389 (q389 ◇ q389) q388 q389)).symm).trans (apc52 q389 q389 ((q389 ◇ q389) ◇ q388))).trans ((cg (fun t => ((q389 ◇ q389) ◇ q388) ◇ t) (apc182 q389 q389)).trans (cg (fun t => ((q389 ◇ q389) ◇ q388) ◇ t) (apc317 q389 ((q389 ◇ q389) ◇ (q389 ◇ q389))))))).symm
  have apc701:=fun (q390 q391:G)=>by
    exact ((((((cg (fun t => (q391 ◇ q391) ◇ t) (cg (fun t => q391 ◇ t) (apc429 ((q391 ◇ q391) ◇ (q391 ◇ (q390 ◇ q391))) ((q391 ◇ q391) ◇ (q391 ◇ (q390 ◇ q391))) ((q391 ◇ q391) ◇ (q391 ◇ (q390 ◇ q391))) ((q391 ◇ q391) ◇ (q391 ◇ (q390 ◇ q391))) ((q391 ◇ q391) ◇ (q391 ◇ (q390 ◇ q391))) q390 q391 ((q391 ◇ q391) ◇ (q391 ◇ (q390 ◇ q391))) ((q391 ◇ q391) ◇ (q391 ◇ (q390 ◇ q391)))))).trans (cg (fun t => (q391 ◇ q391) ◇ t) (apc533 q390 q391))).trans (apc225 q390 q391 q391)).trans (cg (fun t => (q391 ◇ q390) ◇ t) (apc317 q391 ((q391 ◇ q391) ◇ (q391 ◇ q391))))).symm).trans ((((cg (fun t => (q391 ◇ q391) ◇ t) (cg (fun t => q391 ◇ t) (apc21 q390 q390 q390 q390 q391 q391))).symm).trans (apc113 ((q391 ◇ q390) ◇ q390) q391)).trans ((apc428 q391 q391 ((q391 ◇ q390) ◇ q390)).trans (cg (fun t => (((q391 ◇ q390) ◇ q390) ◇ q391) ◇ t) (apc317 q391 ((q391 ◇ q391) ◇ (q391 ◇ q391))))))).symm
  have apc709:=fun (q392 q393:G)=>by
    exact ((apc429 ((q392 ◇ q392) ◇ (q392 ◇ (((q392 ◇ q392) ◇ q393) ◇ q392))) ((q392 ◇ q392) ◇ (q392 ◇ (((q392 ◇ q392) ◇ q393) ◇ q392))) ((q392 ◇ q392) ◇ (q392 ◇ (((q392 ◇ q392) ◇ q393) ◇ q392))) ((q392 ◇ q392) ◇ (q392 ◇ (((q392 ◇ q392) ◇ q393) ◇ q392))) ((q392 ◇ q392) ◇ (q392 ◇ (((q392 ◇ q392) ◇ q393) ◇ q392))) ((q392 ◇ q392) ◇ q393) q392 ((q392 ◇ q392) ◇ (q392 ◇ (((q392 ◇ q392) ◇ q393) ◇ q392))) ((q392 ◇ q392) ◇ (q392 ◇ (((q392 ◇ q392) ◇ q393) ◇ q392)))).symm).trans ((((apc169 ((q392 ◇ q392) ◇ q393) q392 q392 q392).symm).trans (apc1 q392 (q392 ◇ q392) q393 q392)).trans (apc678 q392 q393))
  have apc721:=fun (q394 q395 q396:G)=>by
    exact (((((((cg (fun t => q396 ◇ t) (cg (fun t => (q395 ◇ q395) ◇ t) (cg (fun t => q394 ◇ t) (apc182 q395 q395)))).trans (cg (fun t => q396 ◇ t) (cg (fun t => (q395 ◇ q395) ◇ t) (cg (fun t => q394 ◇ t) (apc317 q395 ((q395 ◇ q395) ◇ (q395 ◇ q395))))))).trans (cg (fun t => q396 ◇ t) (cg (fun t => (q395 ◇ q395) ◇ t) (apc388 q395 q394 (q394 ◇ (q395 ◇ (q395 ◇ q395))))))).trans (cg (fun t => q396 ◇ t) (apc225 q394 q395 q395))).trans (cg (fun t => q396 ◇ t) (cg (fun t => (q395 ◇ q394) ◇ t) (apc317 q395 ((q395 ◇ q395) ◇ (q395 ◇ q395)))))).symm).trans ((((cg (fun t => q396 ◇ t) (cg (fun t => (q395 ◇ q395) ◇ t) (apc26 q395 q395 q394))).symm).trans (apc1 (q395 ◇ q395) q395 (q395 ◇ (q395 ◇ q394)) q396)).trans ((apc593 ((q395 ◇ (q395 ◇ q394)) ◇ ((((q395 ◇ q395) ◇ q395) ◇ q395) ◇ q396)) ((q395 ◇ (q395 ◇ q394)) ◇ ((((q395 ◇ q395) ◇ q395) ◇ q395) ◇ q396)) ((q395 ◇ (q395 ◇ q394)) ◇ ((((q395 ◇ q395) ◇ q395) ◇ q395) ◇ q396)) ((q395 ◇ (q395 ◇ q394)) ◇ ((((q395 ◇ q395) ◇ q395) ◇ q395) ◇ q396)) ((q395 ◇ (q395 ◇ q394)) ◇ ((((q395 ◇ q395) ◇ q395) ◇ q395) ◇ q396)) q395 (q395 ◇ (q395 ◇ q394)) q396).trans (apc594 ((q395 ◇ (q395 ◇ q394)) ◇ ((q395 ◇ (q395 ◇ q395)) ◇ q396)) ((q395 ◇ (q395 ◇ q394)) ◇ ((q395 ◇ (q395 ◇ q395)) ◇ q396)) ((q395 ◇ (q395 ◇ q394)) ◇ ((q395 ◇ (q395 ◇ q395)) ◇ q396)) (q395 ◇ q394) q395 q396 ((q395 ◇ (q395 ◇ q394)) ◇ ((q395 ◇ (q395 ◇ q395)) ◇ q396)) ((q395 ◇ (q395 ◇ q394)) ◇ ((q395 ◇ (q395 ◇ q395)) ◇ q396)) ((q395 ◇ (q395 ◇ q394)) ◇ ((q395 ◇ (q395 ◇ q395)) ◇ q396)) ((q395 ◇ (q395 ◇ q394)) ◇ ((q395 ◇ (q395 ◇ q395)) ◇ q396)) ((q395 ◇ (q395 ◇ q394)) ◇ ((q395 ◇ (q395 ◇ q395)) ◇ q396)))))).symm
  have apc729:=fun (q397 q398:G)=>by
    exact (((apc593 (q397 ◇ ((((q398 ◇ q398) ◇ q398) ◇ q398) ◇ (q398 ◇ q398))) (q397 ◇ ((((q398 ◇ q398) ◇ q398) ◇ q398) ◇ (q398 ◇ q398))) (q397 ◇ ((((q398 ◇ q398) ◇ q398) ◇ q398) ◇ (q398 ◇ q398))) (q397 ◇ ((((q398 ◇ q398) ◇ q398) ◇ q398) ◇ (q398 ◇ q398))) (q397 ◇ ((((q398 ◇ q398) ◇ q398) ◇ q398) ◇ (q398 ◇ q398))) q398 q397 (q398 ◇ q398)).trans (apc442 q398 q397)).symm).trans ((((apc122 q398 q397 (q398 ◇ q398)).symm).trans (apc5 ((q398 ◇ q398) ◇ (q398 ◇ q397)) q398 q398)).trans (((((cg (fun t => q398 ◇ t) (apc655 (q398 ◇ q398) q397 q398)).trans (cg (fun t => q398 ◇ t) (apc696 (q398 ◇ q397) q398))).trans (cg (fun t => q398 ◇ t) (apc721 q397 q398 q398))).trans (cg (fun t => q398 ◇ t) (apc472 q397 q398 (q398 ◇ ((q398 ◇ q397) ◇ (q398 ◇ (q398 ◇ q398)))) (q398 ◇ ((q398 ◇ q397) ◇ (q398 ◇ (q398 ◇ q398)))) (q398 ◇ ((q398 ◇ q397) ◇ (q398 ◇ (q398 ◇ q398)))) (q398 ◇ ((q398 ◇ q397) ◇ (q398 ◇ (q398 ◇ q398)))) (q398 ◇ ((q398 ◇ q397) ◇ (q398 ◇ (q398 ◇ q398)))) (q398 ◇ ((q398 ◇ q397) ◇ (q398 ◇ (q398 ◇ q398)))) (q398 ◇ ((q398 ◇ q397) ◇ (q398 ◇ (q398 ◇ q398)))) (q398 ◇ ((q398 ◇ q397) ◇ (q398 ◇ (q398 ◇ q398)))) (q398 ◇ ((q398 ◇ q397) ◇ (q398 ◇ (q398 ◇ q398)))) (q398 ◇ ((q398 ◇ q397) ◇ (q398 ◇ (q398 ◇ q398)))) (q398 ◇ ((q398 ◇ q397) ◇ (q398 ◇ (q398 ◇ q398)))) (q398 ◇ ((q398 ◇ q397) ◇ (q398 ◇ (q398 ◇ q398)))) (q398 ◇ ((q398 ◇ q397) ◇ (q398 ◇ (q398 ◇ q398))))))).trans (apc533 q397 q398)))
  have apc732:=fun (q397 q398 q340 q341:G)=>by
    exact (apc442 q340 q341).trans (apc729 q341 q340)
  have apc734:=fun (q399 q400 q401:G)=>by
    exact (((cg (fun t => q401 ◇ t) (apc75 (q399 ◇ q399) q400 q399 q399 q399)).trans (cg (fun t => q401 ◇ t) (cg (fun t => q399 ◇ t) (apc729 (q399 ◇ q400) q399)))).symm).trans ((((cg (fun t => q401 ◇ t) (cg (fun t => t ◇ (((q399 ◇ q399) ◇ q399) ◇ q399)) (apc131 q399 q400 q399 q399))).symm).trans ((h q400 (((q399 ◇ q399) ◇ q399) ◇ q399) q401).symm)).trans (apc593 (q400 ◇ ((((q399 ◇ q399) ◇ q399) ◇ q399) ◇ q401)) (q400 ◇ ((((q399 ◇ q399) ◇ q399) ◇ q399) ◇ q401)) (q400 ◇ ((((q399 ◇ q399) ◇ q399) ◇ q399) ◇ q401)) (q400 ◇ ((((q399 ◇ q399) ◇ q399) ◇ q399) ◇ q401)) (q400 ◇ ((((q399 ◇ q399) ◇ q399) ◇ q399) ◇ q401)) q399 q400 q401))
  have apc756:=fun (q402 q403 q404:G)=>by
    exact (((apc135 q404 q402 q403 ((q403 ◇ q403) ◇ ((q404 ◇ (q402 ◇ q403)) ◇ (q402 ◇ q403))) ((q403 ◇ q403) ◇ ((q404 ◇ (q402 ◇ q403)) ◇ (q402 ◇ q403))) ((q403 ◇ q403) ◇ ((q404 ◇ (q402 ◇ q403)) ◇ (q402 ◇ q403)))).symm).trans (((apc269 (q404 ◇ (q402 ◇ q403)) q402 q403).symm).trans ((h q404 (q402 ◇ q403) ((q403 ◇ q403) ◇ q403)).symm))).symm
  have apc787:=fun (q405 q406 q407:G)=>by
    exact (((cg (fun t => q407 ◇ t) (apc225 q405 q406 q406)).trans (cg (fun t => q407 ◇ t) (cg (fun t => (q406 ◇ q405) ◇ t) (apc317 q406 ((q406 ◇ q406) ◇ (q406 ◇ q406)))))).symm).trans ((((cg (fun t => q407 ◇ t) (cg (fun t => (q406 ◇ q406) ◇ t) (apc183 q405 q405 q406 q405))).symm).trans (apc1 (q406 ◇ q406) q406 (q405 ◇ q406) q407)).trans (apc593 ((q405 ◇ q406) ◇ ((((q406 ◇ q406) ◇ q406) ◇ q406) ◇ q407)) ((q405 ◇ q406) ◇ ((((q406 ◇ q406) ◇ q406) ◇ q406) ◇ q407)) ((q405 ◇ q406) ◇ ((((q406 ◇ q406) ◇ q406) ◇ q406) ◇ q407)) ((q405 ◇ q406) ◇ ((((q406 ◇ q406) ◇ q406) ◇ q406) ◇ q407)) ((q405 ◇ q406) ◇ ((((q406 ◇ q406) ◇ q406) ◇ q406) ◇ q407)) q406 (q405 ◇ q406) q407))
  have apc817:=fun (q408 q409 q410:G)=>by
    exact (((apc544 q408 q410 q409).symm).trans (((cg (fun t => ((q408 ◇ q410) ◇ q410) ◇ t) (apc320 q408 q409 q408)).symm).trans (apc662 q409 q408 q409 q409 q410))).symm
  have apc818:=fun (q411 q412 q413 q414:G)=>by
    exact (((cg (fun t => q414 ◇ t) (apc817 q411 q413 q412)).symm).trans (apc593 q411 q411 q411 q411 q411 q413 q414 (q411 ◇ (q413 ◇ (q413 ◇ q412))))).symm
  have apc819:=fun (q415 q416 q417:G)=>by
    exact ((((apc818 q415 q416 q417 q417).symm).trans (apc395 q417 (q415 ◇ (q417 ◇ (q417 ◇ q416))) q415)).trans (apc655 q415 (q417 ◇ q416) q417)).symm
  have apc820:=fun (q418 q419 q420:G)=>by
    exact ((cg (fun t => q420 ◇ t) (apc819 q419 q418 q418)).symm).trans ((h q419 (q418 ◇ (q418 ◇ q418)) q420).symm)
  have apc822:=fun (q421 q422 q423:G)=>by
    exact (((cg (fun t => q423 ◇ t) (cg (fun t => q422 ◇ t) (cg (fun t => q421 ◇ t) (apc317 q422 ((q422 ◇ q422) ◇ (q422 ◇ q422)))))).trans (cg (fun t => q423 ◇ t) (cg (fun t => q422 ◇ t) (apc388 q422 q421 (q421 ◇ (q422 ◇ (q422 ◇ q422))))))).symm).trans ((((cg (fun t => q423 ◇ t) (cg (fun t => q422 ◇ t) ((h q421 (q422 ◇ q422) (q422 ◇ q422)).symm))).symm).trans (apc820 q422 (q421 ◇ (q422 ◇ q422)) q423)).trans (((apc646 q421 q422 q422 q423).trans (cg (fun t => q423 ◇ t) (apc469 q421 q422))).trans (apc787 q421 q422 q423)))
  have apc823:=fun (q421 q422 q423 q399 q400 q401:G)=>by
    exact ((apc822 (q399 ◇ q400) q399 q401).symm).trans (apc734 q399 q400 q401)
  have apc824:=fun (q424 q425 q426:G)=>by
    exact ((cg (fun t => q426 ◇ t) (cg (fun t => q425 ◇ t) (apc284 q425 q424))).symm).trans (apc822 q424 q425 q426)
  have apc825:=fun (q427 q428:G)=>by
    exact (((apc732 (q427 ◇ ((q428 ◇ (q428 ◇ q428)) ◇ (q428 ◇ q428))) (q427 ◇ ((q428 ◇ (q428 ◇ q428)) ◇ (q428 ◇ q428))) q428 q427).symm).trans (((apc823 q427 q427 q427 q428 q427 (q428 ◇ q428)).symm).trans ((h q428 (q428 ◇ q428) ((q428 ◇ q427) ◇ q428)).symm))).symm
  have apc826:=fun (q429 q430 q431:G)=>by
    exact (((cg (fun t => q431 ◇ t) (cg (fun t => (q431 ◇ q431) ◇ t) (cg (fun t => t ◇ q431) ((h q429 q430 q431).symm)))).symm).trans (apc825 ((q429 ◇ q430) ◇ q430) q431)).trans (apc270 q429 q430 q431 ((q431 ◇ q431) ◇ (q431 ◇ ((q429 ◇ q430) ◇ q430))) ((q431 ◇ q431) ◇ (q431 ◇ ((q429 ◇ q430) ◇ q430))) ((q431 ◇ q431) ◇ (q431 ◇ ((q429 ◇ q430) ◇ q430))))
  have apc829:=fun (q421 q422 q423 q101 q102 q103:G)=>by
    exact ((cg (fun t => q103 ◇ t) (apc822 q102 q101 q102)).symm).trans (apc53 q101 q102 q103)
  have apc830:=fun (q432 q433 q434:G)=>by
    exact ((((cg (fun t => q434 ◇ t) (apc824 q432 q433 q433)).trans (cg (fun t => q434 ◇ t) (apc590 ((q432 ◇ q433) ◇ ((q433 ◇ (q433 ◇ q433)) ◇ q433)) ((q432 ◇ q433) ◇ ((q433 ◇ (q433 ◇ q433)) ◇ q433)) ((q432 ◇ q433) ◇ ((q433 ◇ (q433 ◇ q433)) ◇ q433)) ((q432 ◇ q433) ◇ ((q433 ◇ (q433 ◇ q433)) ◇ q433)) ((q432 ◇ q433) ◇ ((q433 ◇ (q433 ◇ q433)) ◇ q433)) q433 (q432 ◇ q433)))).trans (cg (fun t => q434 ◇ t) (apc429 ((q433 ◇ q433) ◇ (q433 ◇ (q432 ◇ q433))) ((q433 ◇ q433) ◇ (q433 ◇ (q432 ◇ q433))) ((q433 ◇ q433) ◇ (q433 ◇ (q432 ◇ q433))) ((q433 ◇ q433) ◇ (q433 ◇ (q432 ◇ q433))) ((q433 ◇ q433) ◇ (q433 ◇ (q432 ◇ q433))) q432 q433 ((q433 ◇ q433) ◇ (q433 ◇ (q432 ◇ q433))) ((q433 ◇ q433) ◇ (q433 ◇ (q432 ◇ q433)))))).symm).trans ((((cg (fun t => q434 ◇ t) (cg (fun t => q433 ◇ t) (cg (fun t => q433 ◇ t) (apc284 q433 q432)))).symm).trans (apc824 (q433 ◇ q432) q433 q434)).trans (apc823 (((q433 ◇ q432) ◇ q433) ◇ ((q433 ◇ (q433 ◇ q433)) ◇ q434)) (((q433 ◇ q432) ◇ q433) ◇ ((q433 ◇ (q433 ◇ q433)) ◇ q434)) (((q433 ◇ q432) ◇ q433) ◇ ((q433 ◇ (q433 ◇ q433)) ◇ q434)) q433 q432 q434))
  have apc832:=fun (q432 q433 q434 q365 q366 q367:G)=>by
    exact (((cg (fun t => q367 ◇ t) (apc830 q365 q367 q366)).symm).trans (apc607 q365 q366 q367)).symm
  have apc834:=fun (q435 q436 q437:G)=>by
    exact (((apc832 q435 q435 q435 q435 q436 q437).symm).trans (apc284 q437 (((q437 ◇ q435) ◇ q435) ◇ q436))).trans ((cg (fun t => q437 ◇ t) (apc4 q437 q437 q435 q436)).trans (apc96 q436 q435 q437))
  have apc835:=fun (q438 q439:G)=>by
    exact ((((cg (fun t => q439 ◇ t) ((h q439 (q439 ◇ q439) q438).symm)).symm).trans (apc834 q438 (q439 ◇ q439) q439)).trans (((cg (fun t => (q439 ◇ q439) ◇ t) (apc388 q439 q438 (q438 ◇ (q439 ◇ (q439 ◇ q439))))).trans (apc225 q438 q439 q439)).trans (cg (fun t => (q439 ◇ q438) ◇ t) (apc317 q439 ((q439 ◇ q439) ◇ (q439 ◇ q439)))))).symm
  have apc869:=fun (q421 q422 q423 q228 q229 q230:G)=>by
    exact (apc164 q228 q229 q230).trans (apc822 (q228 ◇ q228) q229 q230)
  have apc872:=fun (q440 q441 q442 q443 q444:G)=>by
    exact (((cg (fun t => (q443 ◇ q444) ◇ t) (cg (fun t => q442 ◇ t) (cg (fun t => t ◇ q444) ((h q440 q441 q443).symm)))).symm).trans (apc252 q442 ((q440 ◇ q441) ◇ q441) q443 q444)).symm
  have apc873:=fun (q445 q446 q447 q448 q449:G)=>by
    exact (((cg (fun t => q449 ◇ t) (cg (fun t => q447 ◇ t) (cg (fun t => t ◇ (q449 ◇ q448)) ((h q445 q446 q448).symm)))).symm).trans (apc872 q445 q446 q447 q448 q449)).symm
  have apc874:=fun (q450 q451 q452:G)=>by
    exact (((apc873 q450 q451 q452 q452 q452).symm).trans (apc284 q452 ((q450 ◇ (q451 ◇ q452)) ◇ q452))).trans (apc826 q450 q451 q452)
  have apc875:=fun (q453 q454:G)=>by
    exact ((((cg (fun t => q454 ◇ t) ((h q453 (q454 ◇ q454) q454).symm)).symm).trans (apc874 q453 q454 q454)).trans (apc469 q453 q454)).symm
  have apc876:=fun (q455 q456:G)=>by
    exact (((apc875 q455 q456).symm).trans (apc835 q455 q456)).symm
  have apc878:=fun (q424 q425 q426 q455 q456:G)=>by
    exact ((cg (fun t => q426 ◇ t) (apc876 q424 q425)).symm).trans (apc824 q424 q425 q426)
  have apc879:=fun (q457 q458 q459:G)=>by
    exact (((cg (fun t => q459 ◇ t) (cg (fun t => q458 ◇ t) ((h q458 q458 q457).symm))).symm).trans (apc878 q457 q458 q459 q457 q457)).symm
  have apc880:=fun (q460 q461:G)=>by
    exact ((((apc879 q460 q461 q461).symm).trans (apc590 q460 q460 q460 q460 q460 q461 (q460 ◇ q461))).trans (apc429 ((q461 ◇ q461) ◇ (q461 ◇ (q460 ◇ q461))) ((q461 ◇ q461) ◇ (q461 ◇ (q460 ◇ q461))) ((q461 ◇ q461) ◇ (q461 ◇ (q460 ◇ q461))) ((q461 ◇ q461) ◇ (q461 ◇ (q460 ◇ q461))) ((q461 ◇ q461) ◇ (q461 ◇ (q460 ◇ q461))) q460 q461 ((q461 ◇ q461) ◇ (q461 ◇ (q460 ◇ q461))) ((q461 ◇ q461) ◇ (q461 ◇ (q460 ◇ q461))))).symm
  have apc883:=fun (q421 q422 q423 q457 q458 q459 q399 q400 q401:G)=>by
    exact ((apc1 q399 q399 q400 q401).symm).trans (((apc879 (q399 ◇ q400) q399 q401).symm).trans (apc823 q399 q399 q399 q399 q400 q401))
  have apc891:=fun (q462 q463:G)=>by
    exact (((apc428 q463 q463 q462).trans (cg (fun t => (q462 ◇ q463) ◇ t) (apc317 q463 ((q463 ◇ q463) ◇ (q463 ◇ q463))))).symm).trans (((apc879 q462 q463 (q463 ◇ q463)).symm).trans ((h q463 (q463 ◇ q463) (q462 ◇ q463)).symm))
  have apc892:=fun (q464 q465:G)=>by
    exact ((apc891 q464 q465).symm).trans (apc880 q464 q465)
  have apc896:=fun (q466 q467:G)=>by
    exact ((((apc1 q467 q467 q466 q467).trans (apc131 q467 q466 (q466 ◇ (((q467 ◇ q467) ◇ q467) ◇ q467)) (q466 ◇ (((q467 ◇ q467) ◇ q467) ◇ q467)))).symm).trans ((((cg (fun t => q467 ◇ t) (apc892 q466 q467)).symm).trans (apc876 (q466 ◇ q467) q467)).trans (apc756 q466 q467 q467))).symm
  have apc898:=fun (q421 q422 q423 q457 q458 q459 q101 q102 q103:G)=>by
    exact (((cg (fun t => q103 ◇ t) (apc879 q102 q101 q102)).symm).trans (apc829 q101 q101 q101 q101 q102 q103)).symm
  have apc899:=fun (q421 q422 q423 q457 q458 q459 q345 q346 q101 q102 q103:G)=>by
    exact ((apc898 (q345 ◇ (((q346 ◇ (q345 ◇ q345)) ◇ (q345 ◇ q345)) ◇ q345)) (q345 ◇ (((q346 ◇ (q345 ◇ q345)) ◇ (q345 ◇ q345)) ◇ q345)) (q345 ◇ (((q346 ◇ (q345 ◇ q345)) ◇ (q345 ◇ q345)) ◇ q345)) (q345 ◇ (((q346 ◇ (q345 ◇ q345)) ◇ (q345 ◇ q345)) ◇ q345)) (q345 ◇ (((q346 ◇ (q345 ◇ q345)) ◇ (q345 ◇ q345)) ◇ q345)) (q345 ◇ (((q346 ◇ (q345 ◇ q345)) ◇ (q345 ◇ q345)) ◇ q345)) q345 q346 q345).symm).trans (apc465 q345 q346)
  have apc904:=fun (q421 q422 q423 q457 q458 q459 q228 q229 q230:G)=>by
    exact (apc869 q228 q228 q228 q228 q229 q230).trans (apc879 (q228 ◇ q228) q229 q230)
  have apc907:=fun (q468 q469 q470:G)=>by
    exact (((cg (fun t => q470 ◇ t) (cg (fun t => q470 ◇ t) ((h q468 q469 (q470 ◇ q470)).symm))).symm).trans (apc876 ((q468 ◇ q469) ◇ q469) q470)).symm
  have apc908:=fun (q471 q472 q473:G)=>by
    exact ((cg (fun t => q473 ◇ t) ((h q473 q473 ((q471 ◇ q472) ◇ q472)).symm)).symm).trans (apc907 q471 q472 q473)
  have apc909:=fun (q474 q475 q476:G)=>by
    exact (((cg (fun t => q476 ◇ t) (cg (fun t => q476 ◇ t) ((h q474 q475 q476).symm))).symm).trans (apc908 q474 q475 q476)).symm
  have apc919:=fun (q468 q469 q470 q474 q475 q476:G)=>by
    exact (apc907 q468 q469 q470).trans (apc909 q468 q469 q470)
  have apc929:=fun (q477 q478 q479 q480:G)=>by
    exact (((cg (fun t => q480 ◇ t) ((h q477 q478 ((q479 ◇ q479) ◇ q479)).symm)).symm).trans (apc883 q477 q477 q477 q477 q477 q477 q479 q480 ((q477 ◇ q478) ◇ q478))).symm
  have apc931:=fun (q481 q482 q483 q484:G)=>by
    exact (((cg (fun t => q484 ◇ t) (cg (fun t => q481 ◇ t) (apc388 q483 q482 (q482 ◇ (q483 ◇ (q483 ◇ q483)))))).symm).trans (((cg (fun t => q484 ◇ t) ((h q481 q482 (q483 ◇ (q483 ◇ q483))).symm)).symm).trans (apc929 q481 q482 q483 q484))).symm
  have apc932:=fun (q485 q486 q487 q488:G)=>by
    exact (((cg (fun t => q488 ◇ t) (cg (fun t => q485 ◇ t) ((h q487 q487 q486).symm))).symm).trans (apc931 q485 q486 q487 q488)).symm
  have apc933:=fun (q275 q276 q277 q485 q486 q487 q488 q308 q309:G)=>by
    exact (((apc932 q275 q276 q277 q277).symm).trans (apc473 q275 q276 q277 q275 q275)).symm
  have apc945:=fun (q489 q490 q491:G)=>by
    exact (((cg (fun t => t ◇ (q491 ◇ (q491 ◇ q491))) ((h q489 q490 q491).symm)).symm).trans (apc875 ((q489 ◇ q490) ◇ q490) q491)).trans (apc919 q489 q490 q491 (q491 ◇ (((q489 ◇ q490) ◇ q490) ◇ ((q491 ◇ q491) ◇ q491))) (q491 ◇ (((q489 ◇ q490) ◇ q490) ◇ ((q491 ◇ q491) ◇ q491))) (q491 ◇ (((q489 ◇ q490) ◇ q490) ◇ ((q491 ◇ q491) ◇ q491))))
  have apc948:=fun (q292 q293 q294 q489 q490 q491 q360 q361 q357 q358 q359 q335 q336:G)=>by
    exact (((apc945 q292 q293 q294).symm).trans (apc577 q292 q293 q294 q292 q292 q292 q292 q292 q292 q292)).symm
  have apc959:=fun (q492 q493 q494:G)=>by
    exact (((apc96 q492 q493 q494).symm).trans (((cg (fun t => q494 ◇ t) ((h q492 (q493 ◇ q494) (q494 ◇ q494)).symm)).symm).trans (apc948 (q492 ◇ (q493 ◇ q494)) q493 q494 q492 q492 q492 q492 q492 q492 q492 q492 q492 q492))).symm
  have apc960:=fun (q495 q496 q497:G)=>by
    exact (((cg (fun t => q497 ◇ t) ((h q495 (q496 ◇ q497) q497).symm)).symm).trans (apc959 q495 q496 q497)).symm
  have apc962:=fun (q498 q499:G)=>by
    exact ((apc960 q498 q499 q499).symm).trans (apc284 q499 (q499 ◇ q498))
  have apc963:=fun (q500 q501:G)=>by
    exact (((cg (fun t => q501 ◇ t) ((h q501 q501 q500).symm)).symm).trans (apc962 q500 q501)).symm
  have apc967:=fun (q243 q244 q500 q501 q347 q348:G)=>by
    exact (apc471 q243 q244 q243 q243).trans (apc963 q243 q244)
  have apc968:=fun (q243 q244 q500 q501 q347 q348:G)=>by
    exact (apc469 q347 q348).trans (apc967 q347 q348 ((q348 ◇ q347) ◇ (q348 ◇ (q348 ◇ q348))) ((q348 ◇ q347) ◇ (q348 ◇ (q348 ◇ q348))) ((q348 ◇ q347) ◇ (q348 ◇ (q348 ◇ q348))) ((q348 ◇ q347) ◇ (q348 ◇ (q348 ◇ q348))))
  have apc969:=fun (q502 q503:G)=>by
    exact (((apc968 q502 q502 q502 q502 q503 q502).symm).trans (apc960 q502 q503 q502)).symm
  have apc970:=fun (q504 q505:G)=>by
    exact ((cg (fun t => q504 ◇ t) ((h q505 q504 q504).symm)).symm).trans (apc969 q504 q505)
  have apc972:=fun (q506 q507:G)=>by
    exact ((((apc128 q506 q507 q507).trans (apc896 q506 q507)).symm).trans (((apc970 q507 (q506 ◇ (q507 ◇ q507))).symm).trans ((h q506 (q507 ◇ q507) q507).symm))).symm
  have apc973:=fun (q508 q509:G)=>by
    exact ((apc972 q509 q508).symm).trans ((h q508 q508 q509).symm)
  have apc975:=fun (q308 q309 q334 q508 q509:G)=>by
    exact (apc388 q308 q309 q308).trans (apc973 q308 q309)
  have apc976:=fun (q331 q332 q508 q509:G)=>by
    exact (((apc973 q331 q332).symm).trans (apc284 q331 q332)).symm
  have apc977:=fun (q506 q507 q508 q509:G)=>by
    exact (apc972 q506 q507).trans (apc973 q507 q506)
  have apc985:=fun (q397 q398 q508 q509:G)=>by
    exact (apc729 q397 q398).trans (apc973 q398 q397)
  have apc986:=fun (q466 q467 q508 q509:G)=>by
    exact (apc896 q466 q467).trans (apc973 q467 q466)
  have apc992:=fun (q337 q338 q339 q207 q208 q212 q213 q237 q238 q239 q240 q308 q309 q334 q231 q232 q508 q509:G)=>by
    exact (((apc975 q238 ((q238 ◇ q237) ◇ q238) (((q238 ◇ q237) ◇ q238) ◇ (q238 ◇ (q238 ◇ q238))) (((q238 ◇ q237) ◇ q238) ◇ (q238 ◇ (q238 ◇ q238))) (((q238 ◇ q237) ◇ q238) ◇ (q238 ◇ (q238 ◇ q238)))).symm).trans (apc430 q237 q237 q237 q237 q237 q237 q237 q237 q238 q237 q237 q237 q237)).trans (apc973 q238 q237)
  have apc995:=fun (q308 q309 q432 q433 q434 q334 q508 q509:G)=>by
    exact ((cg (fun t => q434 ◇ t) (apc975 q433 (q432 ◇ q433) ((q432 ◇ q433) ◇ (q433 ◇ (q433 ◇ q433))) ((q432 ◇ q433) ◇ (q433 ◇ (q433 ◇ q433))) ((q432 ◇ q433) ◇ (q433 ◇ (q433 ◇ q433))))).symm).trans (apc830 q432 q433 q434)
  have apc996:=fun (q510 q511 q512:G)=>by
    exact (((cg (fun t => q512 ◇ t) ((h q510 q511 (q512 ◇ q512)).symm)).symm).trans (apc976 q512 ((q510 ◇ q511) ◇ q511) q510 q510)).symm
  have apc997:=fun (q513 q514 q515:G)=>by
    exact (((cg (fun t => q515 ◇ t) ((h q513 q514 q515).symm)).symm).trans (apc996 q513 q514 q515)).symm
  have apc999:=fun (q510 q511 q512 q513 q514 q515:G)=>by
    exact (apc996 q510 q511 q512).trans (apc997 q510 q511 q512)
  have apc1001:=fun (q392 q393 q308 q309 q334 q508 q509:G)=>by
    exact (((apc975 q392 (((q392 ◇ q392) ◇ q393) ◇ q392) ((((q392 ◇ q392) ◇ q393) ◇ q392) ◇ (q392 ◇ (q392 ◇ q392))) ((((q392 ◇ q392) ◇ q393) ◇ q392) ◇ (q392 ◇ (q392 ◇ q392))) ((((q392 ◇ q392) ◇ q393) ◇ q392) ◇ (q392 ◇ (q392 ◇ q392)))).symm).trans (apc709 q392 q393)).trans (apc973 q392 q393)
  have apc1002:=fun (q402 q403 q404 q506 q507 q508 q509:G)=>by
    exact ((apc995 (q404 ◇ (q403 ◇ (q403 ◇ (q402 ◇ q403)))) (q404 ◇ (q403 ◇ (q403 ◇ (q402 ◇ q403)))) q402 q403 q404 (q404 ◇ (q403 ◇ (q403 ◇ (q402 ◇ q403)))) (q404 ◇ (q403 ◇ (q403 ◇ (q402 ◇ q403)))) (q404 ◇ (q403 ◇ (q403 ◇ (q402 ◇ q403))))).symm).trans (((cg (fun t => q404 ◇ t) (apc977 (q402 ◇ q403) q403 ((q402 ◇ q403) ◇ ((q403 ◇ q403) ◇ q403)) ((q402 ◇ q403) ◇ ((q403 ◇ q403) ◇ q403)))).symm).trans (apc756 q402 q403 q404))
  have apc1004:=fun (q516 q517 q518:G)=>by
    exact (((cg (fun t => (q518 ◇ q518) ◇ t) ((h q516 q517 q518).symm)).symm).trans (apc973 q518 ((q516 ◇ q517) ◇ q517))).trans (apc999 q516 q517 q518 (q518 ◇ (q518 ◇ ((q516 ◇ q517) ◇ q517))) (q518 ◇ (q518 ◇ ((q516 ◇ q517) ◇ q517))) (q518 ◇ (q518 ◇ ((q516 ◇ q517) ◇ q517))))
  have apc1005:=fun (q275 q276 q277 q485 q486 q487 q488 q516 q517 q518 q308 q309:G)=>by
    exact (((apc1004 q275 q276 q277).symm).trans (apc933 q275 q276 q277 q275 q275 q275 q275 q275 q275)).symm
  have apc1007:=fun (q421 q422 q423 q457 q458 q459 q516 q517 q518 q345 q346 q101 q102 q103:G)=>by
    exact ((apc1005 q346 (q345 ◇ q346) q345 (q345 ◇ (q346 ◇ (q345 ◇ (q345 ◇ (q345 ◇ q346))))) (q345 ◇ (q346 ◇ (q345 ◇ (q345 ◇ (q345 ◇ q346))))) (q345 ◇ (q346 ◇ (q345 ◇ (q345 ◇ (q345 ◇ q346))))) (q345 ◇ (q346 ◇ (q345 ◇ (q345 ◇ (q345 ◇ q346))))) (q345 ◇ (q346 ◇ (q345 ◇ (q345 ◇ (q345 ◇ q346))))) (q345 ◇ (q346 ◇ (q345 ◇ (q345 ◇ (q345 ◇ q346))))) (q345 ◇ (q346 ◇ (q345 ◇ (q345 ◇ (q345 ◇ q346))))) (q345 ◇ (q346 ◇ (q345 ◇ (q345 ◇ (q345 ◇ q346))))) (q345 ◇ (q346 ◇ (q345 ◇ (q345 ◇ (q345 ◇ q346)))))).symm).trans ((apc899 q345 q345 q345 q345 q345 q345 q345 q346 q345 q345 q345).trans (apc1004 q345 q346 q345))
  have apc1016:=fun (q275 q276 q277 q485 q486 q487 q488 q516 q517 q518 q289 q290 q291 q308 q309:G)=>by
    exact ((apc1005 q289 (q289 ◇ q291) q290 (q290 ◇ (q289 ◇ (q290 ◇ (q290 ◇ (q289 ◇ q291))))) (q290 ◇ (q289 ◇ (q290 ◇ (q290 ◇ (q289 ◇ q291))))) (q290 ◇ (q289 ◇ (q290 ◇ (q290 ◇ (q289 ◇ q291))))) (q290 ◇ (q289 ◇ (q290 ◇ (q290 ◇ (q289 ◇ q291))))) (q290 ◇ (q289 ◇ (q290 ◇ (q290 ◇ (q289 ◇ q291))))) (q290 ◇ (q289 ◇ (q290 ◇ (q290 ◇ (q289 ◇ q291))))) (q290 ◇ (q289 ◇ (q290 ◇ (q290 ◇ (q289 ◇ q291))))) (q290 ◇ (q289 ◇ (q290 ◇ (q290 ◇ (q289 ◇ q291))))) (q290 ◇ (q289 ◇ (q290 ◇ (q290 ◇ (q289 ◇ q291)))))).symm).trans (apc242 q289 q290 q291)
  have apc1019:=fun (q519 q520:G)=>by
    exact (((cg (fun t => q519 ◇ t) (apc976 q520 q519 q519 q519)).symm).trans (apc1016 q519 q519 q519 q519 q519 q519 q519 q519 q519 q519 q520 q519 q520 q519 q519)).symm
  have apc1022:=fun (q521 q522 q523:G)=>by
    exact (((cg (fun t => q523 ◇ t) ((h q521 (q523 ◇ q523) q522).symm)).symm).trans (apc997 q522 (q521 ◇ (q523 ◇ q523)) q523)).symm
  have apc1031:=fun (q524 q525 q526:G)=>by
    exact (((cg (fun t => q526 ◇ t) (cg (fun t => q526 ◇ t) (cg (fun t => t ◇ q526) ((h q524 q525 q526).symm)))).symm).trans (apc992 q524 q524 q524 q524 q524 q524 q524 ((q524 ◇ q525) ◇ q525) q526 q524 q524 q524 q524 q524 q524 q524 q524 q524)).trans (apc999 q524 q525 q526 (q526 ◇ (q526 ◇ ((q524 ◇ q525) ◇ q525))) (q526 ◇ (q526 ◇ ((q524 ◇ q525) ◇ q525))) (q526 ◇ (q526 ◇ ((q524 ◇ q525) ◇ q525))))
  have apc1032:=fun (q527 q528 q529:G)=>by
    exact ((cg (fun t => q529 ◇ t) (cg (fun t => q529 ◇ t) (cg (fun t => t ◇ q529) ((h q527 q529 q528).symm)))).symm).trans (apc1031 q528 (q527 ◇ q529) q529)
  have apc1036:=fun (q530 q531 q532:G)=>by
    exact (((apc1005 q531 q530 q532 (q532 ◇ (q531 ◇ (q532 ◇ (q532 ◇ q530)))) (q532 ◇ (q531 ◇ (q532 ◇ (q532 ◇ q530)))) (q532 ◇ (q531 ◇ (q532 ◇ (q532 ◇ q530)))) (q532 ◇ (q531 ◇ (q532 ◇ (q532 ◇ q530)))) (q532 ◇ (q531 ◇ (q532 ◇ (q532 ◇ q530)))) (q532 ◇ (q531 ◇ (q532 ◇ (q532 ◇ q530)))) (q532 ◇ (q531 ◇ (q532 ◇ (q532 ◇ q530)))) (q532 ◇ (q531 ◇ (q532 ◇ (q532 ◇ q530)))) (q532 ◇ (q531 ◇ (q532 ◇ (q532 ◇ q530))))).symm).trans (((cg (fun t => q532 ◇ t) (cg (fun t => q531 ◇ t) (apc992 q530 q530 q530 q530 q530 q530 q530 q530 q532 q530 q530 q530 q530 q530 q530 q530 q530 q530))).symm).trans (apc1005 q531 ((q532 ◇ q530) ◇ q532) q532 q530 q530 q530 q530 q530 q530 q530 q530 q530))).symm
  have apc1037:=fun (q533 q534 q535:G)=>by
    exact ((cg (fun t => q535 ◇ t) ((h (q535 ◇ q533) q535 q534).symm)).symm).trans (apc1036 q533 q534 q535)
  have apc1038:=fun (q536 q537:G)=>by
    exact (((apc1007 (q537 ◇ (q536 ◇ ((q537 ◇ q536) ◇ q537))) (q537 ◇ (q536 ◇ ((q537 ◇ q536) ◇ q537))) (q537 ◇ (q536 ◇ ((q537 ◇ q536) ◇ q537))) (q537 ◇ (q536 ◇ ((q537 ◇ q536) ◇ q537))) (q537 ◇ (q536 ◇ ((q537 ◇ q536) ◇ q537))) (q537 ◇ (q536 ◇ ((q537 ◇ q536) ◇ q537))) (q537 ◇ (q536 ◇ ((q537 ◇ q536) ◇ q537))) (q537 ◇ (q536 ◇ ((q537 ◇ q536) ◇ q537))) (q537 ◇ (q536 ◇ ((q537 ◇ q536) ◇ q537))) q537 q536 (q537 ◇ (q536 ◇ ((q537 ◇ q536) ◇ q537))) (q537 ◇ (q536 ◇ ((q537 ◇ q536) ◇ q537))) (q537 ◇ (q536 ◇ ((q537 ◇ q536) ◇ q537)))).symm).trans (((apc1037 (q537 ◇ q536) q536 q537).symm).trans ((h q537 (q537 ◇ q536) q537).symm))).symm
  have apc1042:=fun (q243 q244 q500 q501 q347 q348 q390 q391:G)=>by
    exact (((apc975 q391 (((q391 ◇ q390) ◇ q390) ◇ q391) ((((q391 ◇ q390) ◇ q390) ◇ q391) ◇ (q391 ◇ (q391 ◇ q391))) ((((q391 ◇ q390) ◇ q390) ◇ q391) ◇ (q391 ◇ (q391 ◇ q391))) ((((q391 ◇ q390) ◇ q390) ◇ q391) ◇ (q391 ◇ (q391 ◇ q391)))).trans (apc136 q391 q390 q391)).symm).trans ((apc701 q390 q391).trans (apc967 q390 q391 ((q391 ◇ q390) ◇ (q391 ◇ (q391 ◇ q391))) ((q391 ◇ q390) ◇ (q391 ◇ (q391 ◇ q391))) ((q391 ◇ q390) ◇ (q391 ◇ (q391 ◇ q391))) ((q391 ◇ q390) ◇ (q391 ◇ (q391 ◇ q391)))))
  have apc1043:=fun (q243 q244 q421 q422 q423 q457 q458 q459 q500 q501 q347 q348 q390 q391 q228 q229 q230:G)=>by
    exact (((cg (fun t => q230 ◇ t) (apc1042 ((q228 ◇ q229) ◇ ((q228 ◇ q229) ◇ (q229 ◇ q229))) ((q228 ◇ q229) ◇ ((q228 ◇ q229) ◇ (q229 ◇ q229))) ((q228 ◇ q229) ◇ ((q228 ◇ q229) ◇ (q229 ◇ q229))) ((q228 ◇ q229) ◇ ((q228 ◇ q229) ◇ (q229 ◇ q229))) ((q228 ◇ q229) ◇ ((q228 ◇ q229) ◇ (q229 ◇ q229))) ((q228 ◇ q229) ◇ ((q228 ◇ q229) ◇ (q229 ◇ q229))) q228 q229)).symm).trans (apc904 q228 q228 q228 q228 q228 q228 q228 q229 q230)).symm
  have apc1044:=fun (q538 q539:G)=>by
    exact (((apc1005 q539 q538 q539 (q539 ◇ (q539 ◇ (q539 ◇ (q539 ◇ q538)))) (q539 ◇ (q539 ◇ (q539 ◇ (q539 ◇ q538)))) (q539 ◇ (q539 ◇ (q539 ◇ (q539 ◇ q538)))) (q539 ◇ (q539 ◇ (q539 ◇ (q539 ◇ q538)))) (q539 ◇ (q539 ◇ (q539 ◇ (q539 ◇ q538)))) (q539 ◇ (q539 ◇ (q539 ◇ (q539 ◇ q538)))) (q539 ◇ (q539 ◇ (q539 ◇ (q539 ◇ q538)))) (q539 ◇ (q539 ◇ (q539 ◇ (q539 ◇ q538)))) (q539 ◇ (q539 ◇ (q539 ◇ (q539 ◇ q538))))).symm).trans (((apc1043 q538 q538 q538 q538 q538 q538 q538 q538 q538 q538 q538 q538 q538 q538 q538 q539 q539).symm).trans (apc1005 q539 (q538 ◇ q538) q539 q538 q538 q538 q538 q538 q538 q538 q538 q538))).symm
  have apc1051:=fun (q540 q541 q542:G)=>by
    exact ((((cg (fun t => q542 ◇ t) (cg (fun t => q541 ◇ t) ((h q540 q541 q541).symm))).symm).trans (apc995 q540 q540 (q540 ◇ q541) q541 q542 q540 q540 q540)).trans (apc879 q540 q541 q542)).symm
  have apc1054:=fun (q543 q544 q545:G)=>by
    exact ((cg (fun t => q545 ◇ t) (apc1051 q543 q545 q544)).symm).trans (apc1005 q544 (q545 ◇ q543) q545 q543 q543 q543 q543 q543 q543 q543 q543 q543)
  have apc1056:=fun (q546 q547 q548:G)=>by
    exact (((apc1005 q547 q546 q548 (q548 ◇ (q547 ◇ (q548 ◇ (q548 ◇ q546)))) (q548 ◇ (q547 ◇ (q548 ◇ (q548 ◇ q546)))) (q548 ◇ (q547 ◇ (q548 ◇ (q548 ◇ q546)))) (q548 ◇ (q547 ◇ (q548 ◇ (q548 ◇ q546)))) (q548 ◇ (q547 ◇ (q548 ◇ (q548 ◇ q546)))) (q548 ◇ (q547 ◇ (q548 ◇ (q548 ◇ q546)))) (q548 ◇ (q547 ◇ (q548 ◇ (q548 ◇ q546)))) (q548 ◇ (q547 ◇ (q548 ◇ (q548 ◇ q546)))) (q548 ◇ (q547 ◇ (q548 ◇ (q548 ◇ q546))))).symm).trans (((cg (fun t => q548 ◇ t) (cg (fun t => q547 ◇ t) (apc986 q546 q548 q546 q546))).symm).trans (apc1054 (q546 ◇ q548) q547 q548))).symm
  have apc1057:=fun (q549 q550 q551:G)=>by
    exact (((apc1022 q549 q550 q551).symm).trans (((cg (fun t => q551 ◇ t) (cg (fun t => q550 ◇ t) (cg (fun t => t ◇ q551) ((h q549 q551 q551).symm)))).symm).trans (apc1056 (q549 ◇ q551) q550 q551))).symm
  have apc1058:=fun (q552 q553 q554:G)=>by
    exact (((cg (fun t => q554 ◇ t) ((h q552 q554 q553).symm)).symm).trans (apc1057 q552 q553 q554)).symm
  have apc1059:=fun (q549 q550 q551 q552 q553 q554:G)=>by
    exact (apc1057 q549 q550 q551).trans (apc1058 q549 q550 q551)
  have apc1064:=fun (q527 q528 q529 q549 q550 q551:G)=>by
    exact ((apc1032 q527 q528 q529).trans (apc1057 q527 q528 q529)).trans (apc1058 q527 q528 q529)
  have apc1065:=fun (q555 q556:G)=>by
    exact ((apc1037 q555 q555 q556).symm).trans ((((apc1064 (q556 ◇ q555) q555 q556 q555 q555 q555).symm).trans (apc1044 (q556 ◇ q555) q556)).trans (((apc1016 (q556 ◇ (q556 ◇ ((q556 ◇ q555) ◇ q556))) (q556 ◇ (q556 ◇ ((q556 ◇ q555) ◇ q556))) (q556 ◇ (q556 ◇ ((q556 ◇ q555) ◇ q556))) (q556 ◇ (q556 ◇ ((q556 ◇ q555) ◇ q556))) (q556 ◇ (q556 ◇ ((q556 ◇ q555) ◇ q556))) (q556 ◇ (q556 ◇ ((q556 ◇ q555) ◇ q556))) (q556 ◇ (q556 ◇ ((q556 ◇ q555) ◇ q556))) (q556 ◇ (q556 ◇ ((q556 ◇ q555) ◇ q556))) (q556 ◇ (q556 ◇ ((q556 ◇ q555) ◇ q556))) (q556 ◇ (q556 ◇ ((q556 ◇ q555) ◇ q556))) q556 q556 q555 (q556 ◇ (q556 ◇ ((q556 ◇ q555) ◇ q556))) (q556 ◇ (q556 ◇ ((q556 ◇ q555) ◇ q556)))).trans (cg (fun t => q555 ◇ t) (apc973 q556 q556))).trans (apc975 q556 q555 (q555 ◇ (q556 ◇ (q556 ◇ q556))) (q555 ◇ (q556 ◇ (q556 ◇ q556))) (q555 ◇ (q556 ◇ (q556 ◇ q556))))))
  have apc1066:=fun (q557 q558:G)=>by
    exact (((apc1065 q557 q558).symm).trans (((cg (fun t => q558 ◇ t) (apc985 q558 q557 q557 q557)).symm).trans (apc1065 (q557 ◇ q557) q558))).symm
  have apc1067:=fun (q555 q556 q519 q520:G)=>by
    exact (apc1019 q519 q520).trans (apc1065 q520 q519)
  have apc1074:=fun (q559 q560 q561:G)=>by
    exact (((apc1005 q560 q559 q561 (q561 ◇ (q560 ◇ (q561 ◇ (q561 ◇ q559)))) (q561 ◇ (q560 ◇ (q561 ◇ (q561 ◇ q559)))) (q561 ◇ (q560 ◇ (q561 ◇ (q561 ◇ q559)))) (q561 ◇ (q560 ◇ (q561 ◇ (q561 ◇ q559)))) (q561 ◇ (q560 ◇ (q561 ◇ (q561 ◇ q559)))) (q561 ◇ (q560 ◇ (q561 ◇ (q561 ◇ q559)))) (q561 ◇ (q560 ◇ (q561 ◇ (q561 ◇ q559)))) (q561 ◇ (q560 ◇ (q561 ◇ (q561 ◇ q559)))) (q561 ◇ (q560 ◇ (q561 ◇ (q561 ◇ q559))))).symm).trans (((cg (fun t => q561 ◇ t) (cg (fun t => q560 ◇ t) (apc1066 q559 q561))).symm).trans (apc1005 q560 (q559 ◇ q559) q561 q559 q559 q559 q559 q559 q559 q559 q559 q559))).symm
  have apc1084:=fun (q562 q563 q564:G)=>by
    exact ((apc1037 q562 (q564 ◇ q563) q564).symm).trans (apc1005 (q564 ◇ q562) q563 q564 q562 q562 q562 q562 q562 q562 q562 q562 q562)
  have apc1086:=fun (q565 q566:G)=>by
    exact (((((apc1059 q565 (q566 ◇ q565) q566 (q566 ◇ ((q566 ◇ q565) ◇ ((q565 ◇ q566) ◇ q566))) (q566 ◇ ((q566 ◇ q565) ◇ ((q565 ◇ q566) ◇ q566))) (q566 ◇ ((q566 ◇ q565) ◇ ((q565 ◇ q566) ◇ q566)))).trans (cg (fun t => q566 ◇ t) (apc1065 q566 q565))).trans (apc1065 q565 q566)).symm).trans (((apc1084 q565 (q565 ◇ q566) q566).symm).trans ((h q566 (q565 ◇ q566) q566).symm))).symm
  have apc1087:=fun (q567 q568:G)=>by
    exact ((apc1086 q567 q568).symm).trans ((h q567 q568 q568).symm)
  have apc1092:=fun (q567 q568 q557 q558:G)=>by
    exact ((apc1087 (q557 ◇ q557) q558).symm).trans ((apc1066 q557 q558).trans (apc1087 q557 q558))
  have apc1098:=fun (q536 q537 q567 q568:G)=>by
    exact ((apc1038 q536 q537).trans (apc1087 (q536 ◇ q537) q537)).symm
  have apc1099:=fun (q567 q568 q392 q393 q308 q309 q334 q508 q509:G)=>by
    exact ((apc1087 (((q392 ◇ q392) ◇ q393) ◇ q392) q392).symm).trans (apc1001 q392 q393 q392 q392 q392 q392 q392)
  have apc1100:=fun (q569 q570:G)=>by
    exact (((apc1087 q569 q570).symm).trans ((((apc1099 q569 q569 q570 q569 q569 q569 q569 q569 q569).symm).trans (apc1098 ((q570 ◇ q570) ◇ q569) q570 q569 q569)).trans ((cg (fun t => q570 ◇ t) (cg (fun t => t ◇ q570) (apc976 q570 q569 (q570 ◇ ((q570 ◇ q570) ◇ q569)) (q570 ◇ ((q570 ◇ q570) ◇ q569))))).trans (cg (fun t => q570 ◇ t) (cg (fun t => t ◇ q570) (apc1087 q569 q570)))))).symm
  have apc1101:=fun (q510 q511 q512 q513 q514 q515 q567 q568:G)=>by
    exact ((apc1087 ((q510 ◇ q511) ◇ q511) q512).symm).trans (apc999 q510 q511 q512 q510 q510 q510)
  have apc1110:=fun (q571 q572:G)=>by
    exact (((apc1087 (q572 ◇ (q571 ◇ q571)) q571).symm).trans (apc997 q571 q572 q571)).trans (apc1087 (q572 ◇ q571) q571)
  have apc1121:=fun (q573 q574 q575:G)=>by
    exact ((cg (fun t => q575 ◇ t) (apc1110 q573 q574)).symm).trans ((h q574 (q573 ◇ q573) q575).symm)
  have apc1122:=fun (q573 q574 q575 q402 q403 q404 q506 q507 q508 q509:G)=>by
    exact (apc1002 q402 q403 q404 q402 q402 q402 q402).trans (apc1121 q403 q402 q404)
  have apc1178:=fun (q576 q577:G)=>by
    exact (((cg (fun t => q577 ◇ t) (cg (fun t => t ◇ q577) (apc975 q576 q577 q576 q576 q576))).symm).trans (apc1038 (q576 ◇ (q576 ◇ q576)) q577)).trans (((cg (fun t => q577 ◇ t) (apc1122 (q577 ◇ ((q576 ◇ (q576 ◇ q576)) ◇ q577)) (q577 ◇ ((q576 ◇ (q576 ◇ q576)) ◇ q577)) (q577 ◇ ((q576 ◇ (q576 ◇ q576)) ◇ q577)) q577 q576 q577 (q577 ◇ ((q576 ◇ (q576 ◇ q576)) ◇ q577)) (q577 ◇ ((q576 ◇ (q576 ◇ q576)) ◇ q577)) (q577 ◇ ((q576 ◇ (q576 ◇ q576)) ◇ q577)) (q577 ◇ ((q576 ◇ (q576 ◇ q576)) ◇ q577)))).trans (apc1074 q576 q577 q577)).trans (apc1087 (q576 ◇ q577) q577))
  have apc1189:=fun (q573 q574 q575 q362 q363 q364 q402 q403 q404 q310 q311 q312 q231 q232 q168 q169 q170 q506 q507 q508 q509:G)=>by
    exact (((apc1122 ((q311 ◇ q310) ◇ ((q311 ◇ (q311 ◇ q311)) ◇ q312)) ((q311 ◇ q310) ◇ ((q311 ◇ (q311 ◇ q311)) ◇ q312)) ((q311 ◇ q310) ◇ ((q311 ◇ (q311 ◇ q311)) ◇ q312)) (q311 ◇ q310) q311 q312 ((q311 ◇ q310) ◇ ((q311 ◇ (q311 ◇ q311)) ◇ q312)) ((q311 ◇ q310) ◇ ((q311 ◇ (q311 ◇ q311)) ◇ q312)) ((q311 ◇ q310) ◇ ((q311 ◇ (q311 ◇ q311)) ◇ q312)) ((q311 ◇ q310) ◇ ((q311 ◇ (q311 ◇ q311)) ◇ q312))).symm).trans (apc594 q310 q310 q310 q310 q311 q312 q310 q310 q310 q310 q310)).trans ((cg (fun t => q312 ◇ t) (apc973 q311 q310)).trans (cg (fun t => q312 ◇ t) (apc1087 q310 q311)))
  have apc1191:=fun (q578 q579 q580:G)=>by
    exact (((cg (fun t => q580 ◇ t) (cg (fun t => t ◇ q580) (apc1101 q578 q579 q580 q578 q578 q578 q578 q578))).symm).trans (apc1100 ((q578 ◇ q579) ◇ q579) q580)).trans (apc1101 q578 q579 q580 (((q578 ◇ q579) ◇ q579) ◇ (q580 ◇ q580)) (((q578 ◇ q579) ◇ q579) ◇ (q580 ◇ q580)) (((q578 ◇ q579) ◇ q579) ◇ (q580 ◇ q580)) (((q578 ◇ q579) ◇ q579) ◇ (q580 ◇ q580)) (((q578 ◇ q579) ◇ q579) ◇ (q580 ◇ q580)))
  have apc1193:=fun (q581 q582 q583:G)=>by
    exact (((cg (fun t => q583 ◇ t) (cg (fun t => t ◇ q583) (cg (fun t => q583 ◇ t) ((h q581 q583 q582).symm)))).symm).trans (apc1191 q582 (q581 ◇ q583) q583)).trans (apc1059 q581 q582 q583 (q583 ◇ (q582 ◇ ((q581 ◇ q583) ◇ q583))) (q583 ◇ (q582 ◇ ((q581 ◇ q583) ◇ q583))) (q583 ◇ (q582 ◇ ((q581 ◇ q583) ◇ q583))))
  have apc1197:=fun (q584 q585:G)=>by
    exact ((apc1178 q584 q585).symm).trans ((((cg (fun t => q585 ◇ t) (cg (fun t => t ◇ q585) (apc1067 q584 q584 q584 q585))).symm).trans (apc1193 (q584 ◇ q585) q584 q585)).trans (apc1067 (q585 ◇ ((q584 ◇ q585) ◇ (q585 ◇ q584))) (q585 ◇ ((q584 ◇ q585) ◇ (q585 ◇ q584))) q584 q585))
  have apc1204:=fun (q584 q585 q573 q574 q575:G)=>by
    exact ((cg (fun t => q575 ◇ t) (apc1087 q573 q574)).symm).trans (((cg (fun t => q575 ◇ t) (apc1197 q574 q573)).symm).trans (apc1121 q573 q574 q575))
  have apc1349:=fun (q586 q587 q588:G)=>by
    exact ((cg (fun t => (q588 ◇ q587) ◇ t) (apc1092 q586 q586 q588 q586)).symm).trans (apc1189 q586 q586 q586 q586 q586 q586 q586 q586 q586 q587 q588 (q586 ◇ q586) q586 q586 q586 q586 q586 q586 q586 q586 q586)
  have apc1400:=fun (q189 q190 q191 q516 q517 q518 q192 q193 q194:G)=>by
    exact (((apc1004 (q189 ◇ (q190 ◇ q191)) q190 q191).symm).trans (apc135 q189 q190 q191 q189 q189 q189)).trans (cg (fun t => q189 ◇ t) (apc1197 q190 q191))
  have apc1401:=fun (q589 q590 q591:G)=>by
    exact ((apc1400 q590 q589 q591 q589 q589 q589 q589 q589 q589).symm).trans ((h q590 (q589 ◇ q591) q591).symm)
  have apc1402:=fun (q592 q593 q594:G)=>by
    exact (((apc1204 (q593 ◇ (q594 ◇ (q592 ◇ q592))) (q593 ◇ (q594 ◇ (q592 ◇ q592))) q594 q592 q593).symm).trans (((cg (fun t => q593 ◇ t) (apc1087 q594 q592)).symm).trans (apc1401 q592 q593 q594))).symm
  have apc1403:=fun (q595 q596 q597:G)=>by
    exact ((apc1402 q595 q597 q596).symm).trans ((h q595 q596 q597).symm)
  have apc1404:=fun (q584 q585 q573 q574 q575 q595 q596 q597:G)=>by
    exact (apc1204 q573 q573 q573 q574 q575).trans (apc1403 q574 q573 q575)
  have apc1405:=fun (q584 q585 q586 q587 q588 q573 q574 q575 q595 q596 q597:G)=>by
    exact (((cg (fun t => q586 ◇ t) (apc1087 q587 q588)).trans (apc1404 (q586 ◇ (q587 ◇ (q588 ◇ q588))) (q586 ◇ (q587 ◇ (q588 ◇ q588))) q587 q588 q586 (q586 ◇ (q587 ◇ (q588 ◇ q588))) (q586 ◇ (q587 ◇ (q588 ◇ q588))) (q586 ◇ (q587 ◇ (q588 ◇ q588))))).symm).trans (((apc1404 ((q588 ◇ q587) ◇ (q588 ◇ (q586 ◇ q586))) ((q588 ◇ q587) ◇ (q588 ◇ (q586 ◇ q586))) q588 q586 (q588 ◇ q587) ((q588 ◇ q587) ◇ (q588 ◇ (q586 ◇ q586))) ((q588 ◇ q587) ◇ (q588 ◇ (q586 ◇ q586))) ((q588 ◇ q587) ◇ (q588 ◇ (q586 ◇ q586)))).symm).trans ((apc1349 q586 q587 q588).trans ((apc1404 ((q586 ◇ q586) ◇ (q587 ◇ (q588 ◇ q588))) ((q586 ◇ q586) ◇ (q587 ◇ (q588 ◇ q588))) q587 q588 (q586 ◇ q586) ((q586 ◇ q586) ◇ (q587 ◇ (q588 ◇ q588))) ((q586 ◇ q586) ◇ (q587 ◇ (q588 ◇ q588))) ((q586 ◇ q586) ◇ (q587 ◇ (q588 ◇ q588)))).trans (apc1404 (q588 ◇ (q587 ◇ (q586 ◇ q586))) (q588 ◇ (q587 ◇ (q586 ◇ q586))) q587 q586 q588 (q588 ◇ (q587 ◇ (q586 ◇ q586))) (q588 ◇ (q587 ◇ (q586 ◇ q586))) (q588 ◇ (q587 ◇ (q586 ◇ q586)))))))
  exact apc1405 (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) z y x (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) (x ◇ (y ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_55348_to_4369 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_55348_to_4369
