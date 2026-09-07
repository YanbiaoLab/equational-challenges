-- Equation60536 → Equation60338
-- Recorded verdict: true
-- Premise: (x ◇ y) ◇ z = (y ◇ x) ◇ (z ◇ x)
-- Conclusion: (x ◇ y) ◇ y = (y ◇ x) ◇ (x ◇ y)
-- Original submission SHA-256: 1cf08c6b42e609680a98aa2f4c9914a8caa4eb97c91646b8dbcced49d55a1f36
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = (y ◇ x) ◇ (z ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), (x ◇ y) ◇ y = (y ◇ x) ◇ (x ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc0:=fun (q0 q1 q2 q3:G)=>by
    exact ((cg (fun t => t ◇ (q3 ◇ (q2 ◇ q0))) ((h q0 q1 q2).symm)).symm).trans ((h (q2 ◇ q0) (q1 ◇ q0) q3).symm)
  have apc1:=fun (q0 q1 q2 q4:G)=>by
    exact ((cg (fun t => (q4 ◇ (q2 ◇ q0)) ◇ t) ((h q0 q1 q2).symm)).symm).trans ((h (q2 ◇ q0) q4 (q1 ◇ q0)).symm)
  have apc2:=fun (q5 q6 q7 q8:G)=>by
    exact (((cg (fun t => ((q6 ◇ q7) ◇ q8) ◇ t) ((h q6 q5 q8).symm)).symm).trans (apc0 q6 q7 q8 (q5 ◇ q6))).symm
  have apc3:=fun (q9 q10 q11 q12:G)=>by
    exact (((cg (fun t => t ◇ (q9 ◇ q10)) ((h q10 q12 q11).symm)).symm).trans (apc2 q9 q10 q11 q12)).symm
  have apc4:=fun (q13 q14 q15 q16:G)=>by
    exact ((apc3 q13 q14 q15 q16).symm).trans ((h q16 (q14 ◇ q15) (q14 ◇ q13)).symm)
  have apc5:=fun (q17 q18 q19:G)=>by
    exact ((apc4 q19 q18 q18 q17).symm).trans ((h q18 (q18 ◇ q17) q19).symm)
  have apc6:=fun (q20 q21:G)=>by
    exact ((apc5 q20 q21 (q21 ◇ q21)).symm).trans ((h (q21 ◇ q21) q20 q21).symm)
  have apc7:=fun (q22 q23 q24 q25 q26:G)=>by
    exact ((apc0 (q24 ◇ q22) (q23 ◇ q22) q25 q26).symm).trans ((((cg (fun t => t ◇ (q26 ◇ (q25 ◇ (q24 ◇ q22)))) (apc0 q22 q23 q24 q25)).symm).trans ((h (q25 ◇ (q24 ◇ q22)) ((q22 ◇ q23) ◇ q24) q26).symm)).trans (cg (fun t => t ◇ q26) (apc1 q22 q23 q24 q25)))
  have apc8:=fun (q27:G)=>by
    exact ((apc6 q27 q27).symm).trans (apc5 q27 q27 q27)
  have apc9:=fun (q5 q6 q7 q8 q9 q10 q11 q12:G)=>by
    exact (apc2 q5 q6 q7 q8).trans (apc3 q5 q6 q7 q8)
  have apc10:=fun (q28 q29 q30:G)=>by
    exact (((cg (fun t => t ◇ (q29 ◇ q30)) ((h q29 q28 q29).symm)).symm).trans (apc5 (q28 ◇ q29) q29 q30)).symm
  have apc11:=fun (q31 q32 q33:G)=>by
    exact (((apc5 q32 q33 (q33 ◇ q31)).symm).trans (((apc4 (q33 ◇ q31) q33 q33 q32).symm).trans (apc3 q31 q33 q32 q33))).symm
  have apc12:=fun (q34 q35 q36 q37:G)=>by
    exact (((cg (fun t => t ◇ (q35 ◇ q36)) ((h q37 q36 q34).symm)).symm).trans (apc4 q35 q36 (q34 ◇ q37) q37)).symm
  have apc13:=fun (q22 q23 q24 q25 q38:G)=>by
    exact ((apc1 (q24 ◇ q22) (q23 ◇ q22) q25 q38).symm).trans (((cg (fun t => (q38 ◇ (q25 ◇ (q24 ◇ q22))) ◇ t) (apc0 q22 q23 q24 q25)).symm).trans ((h (q25 ◇ (q24 ◇ q22)) q38 ((q22 ◇ q23) ◇ q24)).symm))
  have apc14:=fun (q39 q40:G)=>by
    exact (((apc12 q39 q40 q40 q40).symm).trans (apc6 (q39 ◇ q40) q40)).symm
  have apc15:=fun (q41 q42:G)=>by
    exact (((cg (fun t => t ◇ q42) ((h q42 q42 q41).symm)).symm).trans (apc14 q41 q42)).symm
  have apc16:=fun (q41 q42 q39 q40:G)=>by
    exact (apc14 q39 q40).trans (apc15 q39 q40)
  have apc17:=fun (q43 q44 q45:G)=>by
    exact ((((apc9 q44 q45 q43 q45 q43 q43 q43 q43).symm).trans (apc4 q44 q45 (q43 ◇ q45) q45)).trans (apc10 q43 q45 (q45 ◇ q44))).symm
  have apc18:=fun (q46 q47:G)=>by
    exact ((((apc5 q47 q47 (q47 ◇ q46)).trans (apc5 q47 q47 q46)).symm).trans (((apc11 (q47 ◇ q46) q47 q47).symm).trans (apc3 q46 q47 q47 q47))).symm
  have apc19:=fun (q48 q6 q7 q49:G)=>by
    exact ((cg (fun t => t ◇ (q49 ◇ ((q48 ◇ q7) ◇ q6))) ((h q7 q6 q48).symm)).symm).trans (apc0 q6 q7 (q48 ◇ q7) q49)
  have apc20:=fun (q50 q51 q52:G)=>by
    exact (((apc5 (q51 ◇ q52) q50 q51).symm).trans (apc4 q50 q51 (q50 ◇ q50) q52)).symm
  have apc21:=fun (q53 q54 q55 q56:G)=>by
    exact ((cg (fun t => (q56 ◇ ((q53 ◇ q55) ◇ q54)) ◇ t) ((h q55 q54 q53).symm)).symm).trans (apc1 q54 q55 (q53 ◇ q55) q56)
  have apc22:=fun (q57 q5 q48 q8 q49:G)=>by
    exact (((cg (fun t => t ◇ (q49 ◇ (q8 ◇ (q5 ◇ q57)))) (cg (fun t => t ◇ q8) ((h q57 q5 q48).symm))).symm).trans (apc0 (q5 ◇ q57) (q48 ◇ q57) q8 q49)).trans (apc7 q57 q48 q5 q8 q49)
  have apc24:=fun (q58 q59:G)=>by
    exact ((cg (fun t => (q59 ◇ q58) ◇ t) (apc8 q58)).symm).trans ((h q58 q59 ((q58 ◇ q58) ◇ q58)).symm)
  have apc25:=fun (q60 q61:G)=>by
    exact ((apc24 q60 q61).symm).trans ((h q60 q61 (q60 ◇ (q60 ◇ q60))).symm)
  have apc26:=fun (q62:G)=>by
    exact ((apc25 q62 q62).symm).trans ((h q62 q62 (q62 ◇ q62)).symm)
  have apc28:=fun (q63 q64 q65:G)=>by
    exact ((apc12 q63 (q65 ◇ (q63 ◇ q64)) q65 q64).symm).trans ((h (q65 ◇ (q63 ◇ q64)) q64 q65).symm)
  have apc29:=fun (q66 q67:G)=>by
    exact (((apc28 q67 q66 q67).symm).trans ((h q67 (q66 ◇ q67) (q67 ◇ (q67 ◇ q66))).symm)).symm
  have apc30:=fun (q68:G)=>by
    exact ((apc29 q68 q68).symm).trans ((h (q68 ◇ q68) q68 q68).symm)
  have apc33:=fun (q69 q70:G)=>by
    exact (((apc28 q70 q69 q69).symm).trans (apc4 (q69 ◇ (q70 ◇ q69)) q69 q70 q69)).symm
  have apc34:=fun (q71 q72 q73 q74:G)=>by
    exact ((apc4 (q72 ◇ q73) q74 (q74 ◇ q72) q71).symm).trans (apc1 q72 q73 q74 (q74 ◇ q71))
  have apc35:=fun (q75 q76:G)=>by
    exact ((apc34 q75 q76 (q76 ◇ q76) q76).symm).trans ((h (q76 ◇ (q76 ◇ q76)) q75 q76).symm)
  have apc39:=fun (q77 q78 q79 q80 q81:G)=>by
    exact (((apc3 (q78 ◇ q77) (q79 ◇ q77) q80 q81).symm).trans (((cg (fun t => (((q79 ◇ q77) ◇ q80) ◇ q81) ◇ t) (apc0 q77 q78 q79 q81)).symm).trans (apc0 (q79 ◇ q77) q80 q81 ((q77 ◇ q78) ◇ q79)))).symm
  have apc40:=fun (q82 q83 q84 q21:G)=>by
    exact ((cg (fun t => t ◇ (q21 ◇ (q83 ◇ q84))) (apc5 q82 q83 q84)).symm).trans ((h (q83 ◇ q84) (q82 ◇ (q83 ◇ q83)) q21).symm)
  have apc41:=fun (q82 q83 q84 q20:G)=>by
    exact ((cg (fun t => (q20 ◇ (q83 ◇ q84)) ◇ t) (apc5 q82 q83 q84)).symm).trans ((h (q83 ◇ q84) q20 (q82 ◇ (q83 ◇ q83))).symm)
  have apc42:=fun (q85 q28 q86 q30:G)=>by
    exact ((cg (fun t => t ◇ ((q28 ◇ q85) ◇ q30)) (cg (fun t => q86 ◇ t) ((h q85 q28 q28).symm))).symm).trans (apc5 q86 (q28 ◇ q85) q30)
  have apc46:=fun (q87 q88:G)=>by
    exact (((apc24 q87 (q87 ◇ q88)).symm).trans (apc3 (q87 ◇ q87) q87 q88 q87)).symm
  have apc49:=fun (q89 q90 q91:G)=>by
    exact (((cg (fun t => t ◇ (q90 ◇ q91)) (apc6 q89 q90)).symm).trans (((cg (fun t => t ◇ (q90 ◇ q91)) (apc11 q90 q89 q90)).symm).trans (apc5 ((q90 ◇ q90) ◇ q89) q90 q91))).symm
  have apc53:=fun (q92 q93:G)=>by
    exact ((cg (fun t => (q93 ◇ q92) ◇ t) (apc30 q92)).symm).trans ((h q92 q93 ((q92 ◇ (q92 ◇ q92)) ◇ q92)).symm)
  have apc54:=fun (q94 q95:G)=>by
    exact ((apc53 q94 q95).symm).trans ((h q94 q95 ((q94 ◇ q94) ◇ q94)).symm)
  have apc55:=fun (q96:G)=>by
    exact (((apc54 q96 q96).symm).trans ((h q96 q96 (q96 ◇ (q96 ◇ q96))).symm)).trans (apc26 q96)
  have apc60:=fun (q97 q98 q99:G)=>by
    exact ((cg (fun t => (q99 ◇ (q98 ◇ q98)) ◇ t) (apc6 q97 q98)).symm).trans ((h (q98 ◇ q98) q99 (q98 ◇ (q98 ◇ q97))).symm)
  have apc61:=fun (q100 q101 q102:G)=>by
    exact (((cg (fun t => t ◇ (q101 ◇ q102)) (apc6 q100 q102)).symm).trans (apc4 q101 q102 (q102 ◇ q102) (q102 ◇ q100))).symm
  have apc62:=fun (q103 q104 q105 q106:G)=>by
    exact ((cg (fun t => (q106 ◇ q105) ◇ t) (apc10 q103 q104 q105)).symm).trans ((h q105 q106 (q104 ◇ (q104 ◇ (q103 ◇ q104)))).symm)
  have apc63:=fun (q107 q108 q109:G)=>by
    exact ((cg (fun t => (q109 ◇ q108) ◇ t) ((h q108 (q108 ◇ q107) q108).symm)).symm).trans (apc62 q107 q108 q108 q109)
  have apc65:=fun (q110 q111 q53 q112 q56:G)=>by
    exact (((cg (fun t => (q56 ◇ (q112 ◇ (q111 ◇ q110))) ◇ t) (cg (fun t => t ◇ q112) ((h q110 q111 q53).symm))).symm).trans (apc1 (q111 ◇ q110) (q53 ◇ q110) q112 q56)).trans (apc13 q110 q53 q111 q112 q56)
  have apc66:=fun (q113 q114 q115:G)=>by
    exact ((apc63 q113 q114 q115).symm).trans ((h q114 q115 (q114 ◇ (q114 ◇ q113))).symm)
  have apc67:=fun (q107 q108 q109 q113 q114 q115:G)=>by
    exact (apc63 q107 q108 q109).trans (apc66 q107 q108 q109)
  have apc68:=fun (q69 q70 q113 q114 q115:G)=>by
    exact ((apc66 q70 q69 (q69 ◇ q70)).symm).trans (apc33 q69 q70)
  have apc69:=fun (q116 q117:G)=>by
    exact ((apc68 q117 q116 q116 q116 q116).symm).trans ((h (q117 ◇ q116) q117 q117).symm)
  have apc70:=fun (q69 q70 q113 q114 q115 q116 q117:G)=>by
    exact (apc68 q69 q70 q69 q69 q69).trans (apc69 q70 q69)
  have apc75:=fun (q118 q119 q120 q17 q19:G)=>by
    exact ((cg (fun t => t ◇ (q19 ◇ (q118 ◇ q119))) (apc4 q118 q119 q120 q17)).symm).trans ((h (q118 ◇ q119) ((q119 ◇ q17) ◇ q120) q19).symm)
  have apc76:=fun (q121 q122 q123 q124:G)=>by
    exact ((apc75 q121 q121 q122 q123 q124).symm).trans ((h (q121 ◇ q121) (q123 ◇ (q121 ◇ q122)) q124).symm)
  have apc77:=fun (q125 q126 q127:G)=>by
    exact (((cg (fun t => t ◇ q127) ((h q125 q125 (q125 ◇ q126)).symm)).symm).trans (apc76 q125 q125 q126 q127)).symm
  have apc78:=fun (q128 q129 q130:G)=>by
    exact ((cg (fun t => t ◇ q130) (cg (fun t => (q129 ◇ q129) ◇ t) ((h q129 q128 q129).symm))).symm).trans (apc77 q129 (q128 ◇ q129) q130)
  have apc79:=fun (q131 q132 q133 q134 q135:G)=>by
    exact ((cg (fun t => ((q134 ◇ q135) ◇ (q131 ◇ q132)) ◇ t) (apc1 q131 q132 q134 q133)).symm).trans (apc0 q134 q135 (q131 ◇ q132) (q133 ◇ (q134 ◇ q131)))
  have apc80:=fun (q136 q137 q138:G)=>by
    exact (((cg (fun t => t ◇ q138) ((h q137 q137 (q137 ◇ q136)).symm)).symm).trans (apc78 q136 q137 q138)).symm
  have apc82:=fun (q118 q119 q120 q17 q139:G)=>by
    exact ((cg (fun t => (q139 ◇ (q118 ◇ q119)) ◇ t) (apc4 q118 q119 q120 q17)).symm).trans ((h (q118 ◇ q119) q139 ((q119 ◇ q17) ◇ q120)).symm)
  have apc83:=fun (q140 q141 q142 q143:G)=>by
    exact ((apc82 q140 q140 q141 q142 q143).symm).trans ((h (q140 ◇ q140) q143 (q142 ◇ (q140 ◇ q141))).symm)
  have apc84:=fun (q144 q145 q146:G)=>by
    exact (((apc83 q144 q146 q145 q146).symm).trans ((h q146 (q144 ◇ q144) (q144 ◇ q145)).symm)).trans (apc5 q146 q144 q145)
  have apc86:=fun (q147 q148:G)=>by
    exact ((apc0 q148 q148 q148 q147).symm).trans ((((apc83 q148 q148 q147 q148).symm).trans (apc18 (q148 ◇ q147) q148)).trans (apc5 q148 q148 q147))
  have apc87:=fun (q149 q150:G)=>by
    exact ((cg (fun t => t ◇ q149) ((h q150 q150 q150).symm)).symm).trans (apc86 q149 q150)
  have apc89:=fun (q151 q152:G)=>by
    exact (((apc5 q151 q151 q152).symm).trans ((((apc86 (q151 ◇ q152) q151).symm).trans (apc5 (q151 ◇ q151) q151 q152)).trans (apc10 q151 q151 q152))).symm
  have apc92:=fun (q153 q154 q155:G)=>by
    exact ((cg (fun t => ((q154 ◇ q154) ◇ q155) ◇ t) ((h q155 q153 q154).symm)).symm).trans (apc84 q154 (q153 ◇ q155) q155)
  have apc95:=fun (q156 q157 q158:G)=>by
    exact (((apc92 q156 q158 q157).symm).trans (apc4 (q157 ◇ q156) q158 q157 q158)).symm
  have apc98:=fun (q159 q160 q161:G)=>by
    exact ((cg (fun t => t ◇ (q161 ◇ q160)) (apc87 q160 q159)).symm).trans ((h q160 ((q159 ◇ q159) ◇ q159) q161).symm)
  have apc100:=fun (q159 q160 q162:G)=>by
    exact ((cg (fun t => (q162 ◇ q160) ◇ t) (apc87 q160 q159)).symm).trans ((h q160 q162 ((q159 ◇ q159) ◇ q159)).symm)
  have apc102:=fun (q163 q164 q165:G)=>by
    exact ((apc100 q163 q164 q165).symm).trans ((h q164 q165 (q163 ◇ (q163 ◇ q163))).symm)
  have apc103:=fun (q166 q167:G)=>by
    exact ((apc102 q166 q167 q166).symm).trans ((h q166 q167 (q166 ◇ q166)).symm)
  have apc105:=fun (q168 q169 q170 q171 q172:G)=>by
    exact (((cg (fun t => t ◇ ((q171 ◇ q172) ◇ (q168 ◇ q169))) (apc1 q168 q169 q171 q170)).symm).trans (apc1 q171 q172 (q168 ◇ q169) (q170 ◇ (q171 ◇ q168)))).trans (cg (fun t => t ◇ (q172 ◇ q171)) (apc0 q168 q169 q171 q170))
  have apc106:=fun (q173 q174 q175 q176:G)=>by
    exact ((apc105 q173 q173 q174 q175 q176).symm).trans ((h (q173 ◇ q173) ((q175 ◇ q173) ◇ q174) (q175 ◇ q176)).symm)
  have apc107:=fun (q177 q178 q179:G)=>by
    exact ((apc106 q177 q178 q178 q179).symm).trans ((h q178 ((q178 ◇ q177) ◇ (q177 ◇ q177)) q179).symm)
  have apc108:=fun (q180 q181:G)=>by
    exact (((((apc5 (q180 ◇ q180) q180 q181).trans (apc10 q180 q180 q181)).trans (apc89 q180 q181)).symm).trans (((cg (fun t => t ◇ (q180 ◇ q181)) ((h q180 q180 (q180 ◇ q180)).symm)).symm).trans (apc107 q180 q180 q181))).symm
  have apc109:=fun (q182 q183:G)=>by
    exact (((apc108 q182 ((q182 ◇ q182) ◇ q183)).symm).trans (apc5 q182 (q182 ◇ q182) q183)).trans ((cg (fun t => t ◇ q183) (apc55 q182)).trans (apc86 q183 q182))
  have apc111:=fun (q184 q185 q186 q187:G)=>by
    exact (((cg (fun t => t ◇ (q187 ◇ q186)) (cg (fun t => t ◇ q185) ((h q184 q186 q184).symm))).symm).trans (apc106 q184 q185 q186 q187)).symm
  have apc117:=fun (q184 q185 q186 q187 q173 q174 q175 q176:G)=>by
    exact (apc106 q173 q174 q175 q176).trans (apc111 q173 q174 q175 q176)
  have apc121:=fun (q188 q189:G)=>by
    exact (((apc86 (q189 ◇ (q188 ◇ (q188 ◇ q188))) q188).symm).trans (apc84 q188 q189 (q188 ◇ q188))).trans ((apc10 q188 q188 q189).trans (apc89 q188 q189))
  have apc122:=fun (q190 q191 q192:G)=>by
    exact (((apc4 q192 q190 q191 (q190 ◇ q190)).symm).trans (((cg (fun t => t ◇ (q192 ◇ q190)) (apc86 q191 q190)).symm).trans (apc117 q190 q190 q190 q190 q190 q191 q190 q192))).symm
  have apc125:=fun (q193 q194 q195:G)=>by
    exact (((apc100 q193 q194 q195).symm).trans (((cg (fun t => (q195 ◇ q194) ◇ t) (apc108 q193 q194)).symm).trans ((h q194 q195 (q193 ◇ ((q193 ◇ q193) ◇ (q193 ◇ q193)))).symm))).symm
  have apc126:=fun (q196 q197 q198:G)=>by
    exact ((cg (fun t => (q197 ◇ q198) ◇ t) (cg (fun t => q196 ◇ t) ((h q196 q196 q196).symm))).symm).trans (apc125 q196 q197 q198)
  have apc127:=fun (q199 q200:G)=>by
    exact ((((apc1 q200 q200 q200 q199).trans (apc15 q199 q200)).symm).trans (((apc126 q200 q199 (q200 ◇ q200)).symm).trans (apc5 q199 q200 ((q200 ◇ q200) ◇ q200)))).symm
  have apc128:=fun (q199 q200 q87 q88:G)=>by
    exact (apc46 q87 q88).trans (apc127 q88 q87)
  have apc129:=fun (q201 q202 q203 q204 q205:G)=>by
    exact ((cg (fun t => (q205 ◇ (q201 ◇ q202)) ◇ t) (apc3 q201 q202 q203 q204)).symm).trans (((cg (fun t => (q205 ◇ (q201 ◇ q202)) ◇ t) (apc2 q201 q202 q203 q204)).symm).trans ((h (q201 ◇ q202) q205 ((q204 ◇ q202) ◇ (q203 ◇ q202))).symm))
  have apc130:=fun (q206 q207 q208 q209 q210:G)=>by
    exact ((apc129 q206 q207 q208 q209 q210).symm).trans ((h (q206 ◇ q207) q210 ((q207 ◇ q209) ◇ q208)).symm)
  have apc132:=fun (q199 q200 q87 q88 q75 q76:G)=>by
    exact (((apc128 (((q76 ◇ q76) ◇ (q76 ◇ q75)) ◇ ((q76 ◇ q76) ◇ q76)) (((q76 ◇ q76) ◇ (q76 ◇ q75)) ◇ ((q76 ◇ q76) ◇ q76)) q76 (q76 ◇ q75)).symm).trans (apc35 q75 q76)).symm
  have apc133:=fun (q211 q212:G)=>by
    exact (((((apc21 q212 q212 q212 q211).trans (apc122 q212 q211 q212)).trans (apc15 (q212 ◇ q211) q212)).symm).trans (((apc126 q212 q211 ((q212 ◇ q212) ◇ q212)).symm).trans ((h ((q212 ◇ q212) ◇ q212) q211 q212).symm))).symm
  have apc134:=fun (q213 q214 q215 q216:G)=>by
    exact (((cg (fun t => t ◇ ((q214 ◇ q216) ◇ q215)) ((h q214 q214 q213).symm)).symm).trans (apc83 q214 q215 q216 (q213 ◇ q214))).symm
  have apc135:=fun (q217 q218 q219:G)=>by
    exact ((apc134 q219 q219 q217 q218).symm).trans (apc86 (q218 ◇ (q219 ◇ q217)) q219)
  have apc138:=fun (q220 q221 q222:G)=>by
    exact (((apc135 q220 q221 q222).symm).trans (apc87 ((q222 ◇ q221) ◇ q220) q222)).symm
  have apc139:=fun (q193 q194 q223:G)=>by
    exact (((apc98 q193 q194 q223).symm).trans (((cg (fun t => t ◇ (q223 ◇ q194)) (apc108 q193 q194)).symm).trans ((h q194 (q193 ◇ ((q193 ◇ q193) ◇ (q193 ◇ q193))) q223).symm))).symm
  have apc140:=fun (q224 q225 q226:G)=>by
    exact ((cg (fun t => t ◇ q226) (cg (fun t => q225 ◇ t) (cg (fun t => q224 ◇ t) ((h q224 q224 q224).symm)))).symm).trans (apc139 q224 q225 q226)
  have apc141:=fun (q227 q228 q229 q230 q231:G)=>by
    exact (((cg (fun t => t ◇ ((q231 ◇ q229) ◇ (q230 ◇ q229))) ((h q229 q228 q227).symm)).symm).trans (apc130 q228 q229 q230 q231 (q227 ◇ q229))).symm
  have apc142:=fun (q232 q233 q234 q235 q236:G)=>by
    exact (((cg (fun t => t ◇ ((q234 ◇ q236) ◇ q235)) ((h q234 q233 q232).symm)).symm).trans (apc141 q232 q233 q234 q235 q236)).symm
  have apc143:=fun (q227 q228 q229 q230 q231 q232 q233 q234 q235 q236:G)=>by
    exact (apc141 q227 q228 q229 q230 q231).trans (apc142 q227 q228 q229 q230 q231)
  have apc160:=fun (q237 q238 q239 q240 q241:G)=>by
    exact ((apc0 (q239 ◇ q238) q237 q240 q241).symm).trans (((cg (fun t => t ◇ (q241 ◇ (q240 ◇ (q239 ◇ q238)))) (cg (fun t => t ◇ q240) ((h q239 q238 q237).symm))).symm).trans (apc22 q238 q239 (q237 ◇ q239) q240 q241))
  have apc161:=fun (q242 q243 q244 q245 q246:G)=>by
    exact (((cg (fun t => t ◇ q246) ((h (q244 ◇ q243) q245 q242).symm)).symm).trans (apc160 q242 q243 q244 q245 q246)).symm
  have apc162:=fun (q247 q248 q249 q250:G)=>by
    exact ((cg (fun t => t ◇ q250) ((h q248 (q249 ◇ q248) (q247 ◇ q249)).symm)).symm).trans (apc161 q247 q248 q249 q248 q250)
  have apc163:=fun (q251 q252:G)=>by
    exact (((cg (fun t => t ◇ q252) (apc5 q251 q251 q251)).symm).trans (apc162 q251 q251 q251 q252)).symm
  have apc166:=fun (q242 q243 q244 q245 q246 q237 q238 q239 q240 q241:G)=>by
    exact (apc160 q237 q238 q239 q240 q241).trans (apc161 q237 q238 q239 q240 q241)
  have apc169:=fun (q253 q247 q248 q249 q250:G)=>by
    exact ((cg (fun t => t ◇ q250) (cg (fun t => t ◇ ((q247 ◇ q249) ◇ q248)) ((h q248 q249 q253).symm))).symm).trans (apc161 q247 q248 q249 (q253 ◇ q248) q250)
  have apc170:=fun (q254 q255 q256 q257:G)=>by
    exact ((cg (fun t => t ◇ q257) ((h q255 (q255 ◇ q256) (q254 ◇ q256)).symm)).symm).trans (apc169 q255 q254 q255 q256 q257)
  have apc175:=fun (q258 q259 q260 q261 q262:G)=>by
    exact (((cg (fun t => t ◇ ((q258 ◇ q259) ◇ q260)) ((h (q260 ◇ q258) q262 q261).symm)).symm).trans (apc39 q258 q259 q260 q261 q262)).symm
  have apc179:=fun (q263 q264 q265 q266:G)=>by
    exact ((apc79 q263 q263 q264 q265 q266).symm).trans ((h (q263 ◇ q263) (q265 ◇ q266) ((q265 ◇ q263) ◇ q264)).symm)
  have apc180:=fun (q267 q268 q269 q270:G)=>by
    exact ((cg (fun t => t ◇ (q268 ◇ (q269 ◇ q267))) ((h q269 (q267 ◇ q267) q270).symm)).symm).trans (apc179 q267 q268 q269 q270)
  have apc190:=fun (q13 q14 q15 q271 q272:G)=>by
    exact (((cg (fun t => t ◇ (q272 ◇ ((q14 ◇ q13) ◇ q271))) (apc3 q13 q14 q15 q271)).symm).trans ((h ((q14 ◇ q13) ◇ q271) ((q14 ◇ q15) ◇ q271) q272).symm)).trans (cg (fun t => t ◇ q272) (apc3 q15 q14 q13 q271))
  have apc191:=fun (q273 q274 q275 q276:G)=>by
    exact ((cg (fun t => t ◇ (q276 ◇ ((q274 ◇ q273) ◇ q275))) ((h q274 (q274 ◇ q275) q273).symm)).symm).trans (apc190 q273 q274 q274 q275 q276)
  have apc193:=fun (q103 q106 q277:G)=>by
    exact ((apc10 q103 q106 (q277 ◇ (q106 ◇ (q103 ◇ q106)))).symm).trans ((h (q106 ◇ (q103 ◇ q106)) q106 q277).symm)
  have apc195:=fun (q278 q279:G)=>by
    exact (((apc193 q279 q279 q278).symm).trans (apc89 q279 (q278 ◇ (q279 ◇ (q279 ◇ q279))))).trans (apc121 q279 q278)
  have apc197:=fun (q103 q104 q105 q277:G)=>by
    exact ((cg (fun t => t ◇ (q277 ◇ q105)) (apc10 q103 q104 q105)).symm).trans ((h q105 (q104 ◇ (q104 ◇ (q103 ◇ q104))) q277).symm)
  have apc198:=fun (q280 q281 q282 q283 q284:G)=>by
    exact (((cg (fun t => t ◇ (((q281 ◇ q280) ◇ q283) ◇ q284)) (cg (fun t => t ◇ q284) ((h q280 q281 q282).symm))).symm).trans (apc3 q283 (q281 ◇ q280) (q282 ◇ q280) q284)).symm
  have apc199:=fun (q285 q286 q287:G)=>by
    exact ((((apc4 q287 q286 q286 (q286 ◇ q285)).trans (apc5 (q286 ◇ q285) q286 q287)).symm).trans (((cg (fun t => t ◇ (q287 ◇ q286)) ((h q286 (q286 ◇ q285) q286).symm)).symm).trans (apc197 q285 q286 q286 q287))).symm
  have apc200:=fun (q288 q289 q290 q291:G)=>by
    exact ((apc198 q288 q289 q289 q291 q290).symm).trans ((h (q289 ◇ q288) ((q289 ◇ q288) ◇ q290) q291).symm)
  have apc201:=fun (q292 q293 q294:G)=>by
    exact (((apc98 q292 q293 q294).symm).trans (((cg (fun t => t ◇ (q294 ◇ q293)) (apc89 q292 q293)).symm).trans (apc197 q292 q292 q293 q294))).symm
  have apc202:=fun (q280 q281 q282 q295 q284:G)=>by
    exact (((cg (fun t => (((q281 ◇ q280) ◇ q295) ◇ q284) ◇ t) (cg (fun t => t ◇ q284) ((h q280 q281 q282).symm))).symm).trans (apc3 (q282 ◇ q280) (q281 ◇ q280) q295 q284)).trans (apc175 q280 q282 q281 q295 q284)
  have apc203:=fun (q280 q281 q282 q295 q284 q288 q289 q290 q291:G)=>by
    exact ((apc202 q289 q288 q291 q289 q290).symm).trans (apc200 q288 q289 q290 q291)
  have apc205:=fun (q296 q297 q298 q299 q300:G)=>by
    exact ((apc202 q296 q297 q298 q299 q300).symm).trans ((h q300 ((q297 ◇ q296) ◇ q299) ((q296 ◇ q297) ◇ q298)).symm)
  have apc206:=fun (q301 q302 q303 q304:G)=>by
    exact ((apc205 q301 q304 q302 q304 q303).symm).trans ((h q304 ((q304 ◇ q301) ◇ q303) (q301 ◇ q302)).symm)
  have apc214:=fun (q305 q306 q307:G)=>by
    exact ((((cg (fun t => t ◇ (q307 ◇ q306)) (apc195 q306 q305)).trans (apc98 q305 q306 q307)).symm).trans (((cg (fun t => t ◇ (q307 ◇ q306)) (apc163 q305 q306)).symm).trans ((h q306 (((q305 ◇ q305) ◇ q305) ◇ q305) q307).symm))).symm
  have apc215:=fun (q308 q309 q310:G)=>by
    exact ((cg (fun t => t ◇ q310) (cg (fun t => q309 ◇ t) (apc8 q308))).symm).trans (apc214 q308 q309 q310)
  have apc219:=fun (q311 q312 q313:G)=>by
    exact ((cg (fun t => t ◇ q313) ((h q312 q311 (q312 ◇ (q312 ◇ q312))).symm)).symm).trans (apc215 q312 (q311 ◇ q312) q313)
  have apc220:=fun (q305 q306 q314:G)=>by
    exact ((((cg (fun t => (q314 ◇ q306) ◇ t) (apc195 q306 q305)).trans (apc100 q305 q306 q314)).symm).trans (((cg (fun t => (q314 ◇ q306) ◇ t) (apc163 q305 q306)).symm).trans ((h q306 q314 (((q305 ◇ q305) ◇ q305) ◇ q305)).symm))).symm
  have apc221:=fun (q315 q316 q317:G)=>by
    exact ((cg (fun t => (q316 ◇ q317) ◇ t) (apc8 q315)).symm).trans (apc220 q315 q316 q317)
  have apc223:=fun (q318 q319:G)=>by
    exact ((apc221 q318 q319 q318).symm).trans ((h q318 q319 (q318 ◇ (q318 ◇ q318))).symm)
  have apc224:=fun (q320 q321:G)=>by
    exact ((apc223 q320 q321).symm).trans ((h q320 q321 (q320 ◇ q320)).symm)
  have apc225:=fun (q320 q321 q60 q61:G)=>by
    exact (apc25 q60 q61).trans (apc224 q60 q61)
  have apc226:=fun (q318 q319 q320 q321:G)=>by
    exact (apc223 q318 q319).trans (apc224 q318 q319)
  have apc232:=fun (q322 q323 q324:G)=>by
    exact (((cg (fun t => t ◇ (q324 ◇ q323)) (apc16 q322 q322 q322 q323)).symm).trans ((h q323 ((q323 ◇ q323) ◇ (q322 ◇ q323)) q324).symm)).symm
  have apc233:=fun (q325 q326 q327:G)=>by
    exact (((cg (fun t => t ◇ q327) (cg (fun t => q326 ◇ t) ((h q326 q326 q325).symm))).symm).trans (apc232 q325 q326 q327)).symm
  have apc234:=fun (q325 q326 q327 q322 q323 q324:G)=>by
    exact (apc232 q322 q323 q324).trans (apc233 q322 q323 q324)
  have apc235:=fun (q322 q323 q328:G)=>by
    exact ((cg (fun t => (q328 ◇ q323) ◇ t) (apc16 q322 q322 q322 q323)).symm).trans ((h q323 q328 ((q323 ◇ q323) ◇ (q322 ◇ q323))).symm)
  have apc236:=fun (q329 q330 q331:G)=>by
    exact ((apc235 q329 q330 q331).symm).trans ((h q330 q331 ((q330 ◇ q330) ◇ q329)).symm)
  have apc238:=fun (q322 q323 q328 q329 q330 q331:G)=>by
    exact (apc235 q322 q323 q328).trans (apc236 q322 q323 q328)
  have apc239:=fun (q332 q333:G)=>by
    exact (((apc10 q332 q333 (q333 ◇ (q333 ◇ q332))).trans (apc17 q332 (q333 ◇ q332) q333)).symm).trans ((((apc66 q332 q333 (q333 ◇ (q332 ◇ q333))).symm).trans ((h (q333 ◇ (q332 ◇ q333)) q333 q333).symm)).trans (apc69 q332 q333))
  have apc248:=fun (q334 q335:G)=>by
    exact ((((apc1 q334 (q334 ◇ q334) q334 q335).trans (apc128 (((q334 ◇ q334) ◇ q335) ◇ ((q334 ◇ q334) ◇ q334)) (((q334 ◇ q334) ◇ q335) ◇ ((q334 ◇ q334) ◇ q334)) q334 q335)).symm).trans (((cg (fun t => (q335 ◇ (q334 ◇ q334)) ◇ t) (apc8 q334)).symm).trans (apc60 q334 q334 q335))).symm
  have apc250:=fun (q336 q337 q338:G)=>by
    exact ((((apc3 (q337 ◇ q336) q337 q337 q338).trans (apc3 q336 q337 q338 q337)).symm).trans (((cg (fun t => ((q337 ◇ q337) ◇ q338) ◇ t) (apc5 q336 q337 q338)).symm).trans (apc84 q337 (q336 ◇ (q337 ◇ q337)) q338))).symm
  have apc251:=fun (q339 q340 q341:G)=>by
    exact (((cg (fun t => (q340 ◇ (q340 ◇ q341)) ◇ t) ((h q340 q339 q340).symm)).symm).trans (apc250 (q339 ◇ q340) q340 q341)).symm
  have apc265:=fun (q342 q343 q34 q35 q344:G)=>by
    exact (((cg (fun t => t ◇ (q35 ◇ (q343 ◇ q342))) (cg (fun t => t ◇ q344) ((h q342 q343 q34).symm))).symm).trans (apc4 q35 (q343 ◇ q342) q344 (q34 ◇ q342))).symm
  have apc269:=fun (q345 q346 q347:G)=>by
    exact (((apc4 q345 q346 q347 (q346 ◇ q346)).symm).trans ((((cg (fun t => t ◇ (q345 ◇ q346)) (apc108 q346 q347)).symm).trans (apc4 q345 q346 q347 ((q346 ◇ q346) ◇ (q346 ◇ q346)))).trans (((cg (fun t => t ◇ (q346 ◇ q345)) (apc5 (q346 ◇ q346) q346 q347)).trans (cg (fun t => t ◇ (q346 ◇ q345)) (apc10 q346 q346 q347))).trans (cg (fun t => t ◇ (q346 ◇ q345)) (apc89 q346 q347))))).symm
  have apc271:=fun (q348 q349:G)=>by
    exact ((apc269 q348 q349 q348).symm).trans ((h q348 (q349 ◇ (q349 ◇ q349)) q349).symm)
  have apc273:=fun (q350 q351 q352 q353:G)=>by
    exact (((cg (fun t => t ◇ ((q350 ◇ q353) ◇ q352)) ((h q353 q351 (q350 ◇ q353)).symm)).symm).trans (apc265 q353 q350 q351 q352 q353)).symm
  have apc280:=fun (q354 q355 q356 q357 q358:G)=>by
    exact (((cg (fun t => t ◇ (q358 ◇ ((q354 ◇ q355) ◇ (q355 ◇ q356)))) (apc4 q354 q355 q357 q356)).symm).trans (apc0 (q355 ◇ q356) q357 (q354 ◇ q355) q358)).trans (apc166 ((((q354 ◇ q355) ◇ (q355 ◇ q356)) ◇ (q357 ◇ (q355 ◇ q356))) ◇ q358) ((((q354 ◇ q355) ◇ (q355 ◇ q356)) ◇ (q357 ◇ (q355 ◇ q356))) ◇ q358) ((((q354 ◇ q355) ◇ (q355 ◇ q356)) ◇ (q357 ◇ (q355 ◇ q356))) ◇ q358) ((((q354 ◇ q355) ◇ (q355 ◇ q356)) ◇ (q357 ◇ (q355 ◇ q356))) ◇ q358) ((((q354 ◇ q355) ◇ (q355 ◇ q356)) ◇ (q357 ◇ (q355 ◇ q356))) ◇ q358) q357 q356 q355 (q354 ◇ q355) q358)
  have apc282:=fun (q359 q360 q361:G)=>by
    exact ((apc102 q359 (q359 ◇ q361) q360).symm).trans (apc4 (q359 ◇ q359) q359 q360 q361)
  have apc284:=fun (q362 q363:G)=>by
    exact (((apc233 q363 q362 q362).symm).trans ((((apc61 q363 q362 q362).symm).trans (apc4 q362 q362 (q362 ◇ (q362 ◇ q362)) q363)).trans (apc201 q362 q363 (q362 ◇ q362)))).symm
  have apc285:=fun (q364 q365:G)=>by
    exact (((apc5 (q365 ◇ q364) q365 q365).symm).trans ((((cg (fun t => t ◇ (q365 ◇ q365)) ((h q365 q364 (q365 ◇ q365)).symm)).symm).trans (apc284 q365 (q364 ◇ q365))).trans (apc234 ((q365 ◇ ((q365 ◇ q365) ◇ (q364 ◇ q365))) ◇ q365) ((q365 ◇ ((q365 ◇ q365) ◇ (q364 ◇ q365))) ◇ q365) ((q365 ◇ ((q365 ◇ q365) ◇ (q364 ◇ q365))) ◇ q365) q364 q365 q365))).symm
  have apc286:=fun (q366 q356 q367 q357 q368:G)=>by
    exact (((cg (fun t => ((q367 ◇ q357) ◇ q368) ◇ t) (apc4 q368 q367 q366 q356)).symm).trans (apc0 q367 q357 q368 ((q367 ◇ q356) ◇ q366))).trans (apc143 q357 q368 q367 q366 q356 (((q368 ◇ q367) ◇ (q357 ◇ q367)) ◇ ((q367 ◇ q356) ◇ q366)) (((q368 ◇ q367) ◇ (q357 ◇ q367)) ◇ ((q367 ◇ q356) ◇ q366)) (((q368 ◇ q367) ◇ (q357 ◇ q367)) ◇ ((q367 ◇ q356) ◇ q366)) (((q368 ◇ q367) ◇ (q357 ◇ q367)) ◇ ((q367 ◇ q356) ◇ q366)) (((q368 ◇ q367) ◇ (q357 ◇ q367)) ◇ ((q367 ◇ q356) ◇ q366)))
  have apc287:=fun (q369 q370 q371:G)=>by
    exact (((apc238 q369 q371 (q371 ◇ q370) (((q371 ◇ q370) ◇ q371) ◇ (((q371 ◇ q371) ◇ q369) ◇ q371)) (((q371 ◇ q370) ◇ q371) ◇ (((q371 ◇ q371) ◇ q369) ◇ q371)) (((q371 ◇ q370) ◇ q371) ◇ (((q371 ◇ q371) ◇ q369) ◇ q371))).symm).trans (((cg (fun t => ((q371 ◇ q370) ◇ q371) ◇ t) (apc6 q369 q371)).symm).trans (apc286 q369 q371 q371 q370 q371))).symm
  have apc288:=fun (q372 q373:G)=>by
    exact (((apc287 q373 q373 q372).symm).trans ((h q373 (q372 ◇ q372) (q372 ◇ q372)).symm)).trans (apc5 q373 q372 q372)
  have apc289:=fun (q374 q375:G)=>by
    exact (((apc10 q374 q375 ((q375 ◇ q375) ◇ q374)).trans (apc19 q375 q374 q375 q375)).symm).trans ((((cg (fun t => (q375 ◇ (q375 ◇ (q374 ◇ q375))) ◇ t) ((h q375 q375 q374).symm)).symm).trans (apc288 q375 (q374 ◇ q375))).trans (apc10 q374 q375 q375))
  have apc290:=fun (q376 q377:G)=>by
    exact ((cg (fun t => t ◇ q377) ((h q376 (q377 ◇ q377) q377).symm)).symm).trans (apc289 q376 q377)
  have apc292:=fun (q378 q379:G)=>by
    exact (((cg (fun t => t ◇ q379) (cg (fun t => t ◇ q379) ((h q379 q378 q379).symm))).symm).trans (apc290 (q378 ◇ q379) q379)).trans (((apc4 q379 q379 q379 (q378 ◇ q379)).trans (apc5 (q378 ◇ q379) q379 q379)).trans (apc10 q378 q379 q379))
  have apc319:=fun (q380 q254 q255 q256 q257:G)=>by
    exact (((apc161 q254 q255 q256 q380 q257).symm).trans (((cg (fun t => t ◇ q257) (cg (fun t => t ◇ ((q254 ◇ q256) ◇ q255)) ((h q256 q255 q380).symm))).symm).trans (apc169 (q380 ◇ q256) q254 q255 q256 q257))).symm
  have apc320:=fun (q381 q382 q383 q384 q385:G)=>by
    exact ((cg (fun t => t ◇ q385) (cg (fun t => t ◇ q382) ((h q383 q384 (q381 ◇ q384)).symm))).symm).trans (apc319 q381 q382 q383 q384 q385)
  have apc321:=fun (q254 q255 q256 q257 q381 q382 q383 q384 q385:G)=>by
    exact (apc170 q254 q255 q256 q257).trans (apc320 q255 q254 q256 q255 q257)
  have apc323:=fun (q386 q387 q388 q389 q390:G)=>by
    exact (((apc320 q386 q389 q387 q388 (q390 ◇ q389)).symm).trans ((h q389 ((q387 ◇ q388) ◇ (q386 ◇ q388)) q390).symm)).symm
  have apc326:=fun (q391 q392 q393 q394 q395:G)=>by
    exact (((cg (fun t => t ◇ q395) (cg (fun t => q394 ◇ t) ((h q393 q392 q391).symm))).symm).trans (apc323 q391 q392 q393 q394 q395)).symm
  have apc327:=fun (q391 q392 q393 q394 q395 q386 q387 q388 q389 q390:G)=>by
    exact (apc323 q386 q387 q388 q389 q390).trans (apc326 q386 q387 q388 q389 q390)
  have apc333:=fun (q396 q397 q398 q399 q400:G)=>by
    exact (((apc130 q397 q398 q399 q400 q396).symm).trans (((cg (fun t => t ◇ ((q400 ◇ q398) ◇ (q399 ◇ q398))) ((h q397 q398 q396).symm)).symm).trans (apc142 (q396 ◇ q397) q397 q398 q399 q400))).symm
  have apc342:=fun (q401 q402 q403:G)=>by
    exact (((apc238 (q402 ◇ q401) q402 q403 ((q403 ◇ q402) ◇ (((q402 ◇ q402) ◇ (q402 ◇ q401)) ◇ q402)) ((q403 ◇ q402) ◇ (((q402 ◇ q402) ◇ (q402 ◇ q401)) ◇ q402)) ((q403 ◇ q402) ◇ (((q402 ◇ q402) ◇ (q402 ◇ q401)) ◇ q402))).symm).trans (((cg (fun t => (q403 ◇ q402) ◇ t) (apc133 q401 q402)).symm).trans ((h q402 q403 (((q402 ◇ q402) ◇ q402) ◇ q401)).symm))).symm
  have apc343:=fun (q404 q405:G)=>by
    exact (((apc342 q404 q405 q404).symm).trans ((h q404 q405 ((q405 ◇ q405) ◇ q405)).symm)).trans (apc226 q405 q404 ((q404 ◇ q405) ◇ ((q405 ◇ q405) ◇ q405)) ((q404 ◇ q405) ◇ ((q405 ◇ q405) ◇ q405)))
  have apc345:=fun (q406 q407 q408:G)=>by
    exact ((cg (fun t => (q407 ◇ q408) ◇ t) (apc87 q406 q407)).symm).trans (apc342 q406 q407 q408)
  have apc347:=fun (q409 q410 q411:G)=>by
    exact (((cg (fun t => t ◇ ((q409 ◇ (q409 ◇ q409)) ◇ q411)) (cg (fun t => q410 ◇ t) (apc5 q409 q409 q409))).trans (apc215 q409 q410 ((q409 ◇ (q409 ◇ q409)) ◇ q411))).symm).trans ((((cg (fun t => t ◇ ((q409 ◇ (q409 ◇ q409)) ◇ q411)) (cg (fun t => q410 ◇ t) (apc5 q409 q409 (q409 ◇ q409)))).symm).trans (apc5 q410 (q409 ◇ (q409 ◇ q409)) q411)).trans (((cg (fun t => t ◇ q411) (apc138 q410 (q409 ◇ q409) q409)).trans (cg (fun t => t ◇ q411) (apc109 q409 (q409 ◇ q410)))).trans (cg (fun t => t ◇ q411) (apc5 q409 q409 q410))))
  have apc374:=fun (q412 q413 q414:G)=>by
    exact ((apc206 q412 ((q413 ◇ q412) ◇ q413) q414 q413).symm).trans ((h ((q413 ◇ q412) ◇ q413) q414 (q412 ◇ q413)).symm)
  have apc375:=fun (q415 q416:G)=>by
    exact (((apc326 q415 q416 q415 q415 q416).symm).trans (((apc374 q416 q415 q415).symm).trans ((h ((q415 ◇ q416) ◇ q415) q415 q416).symm))).symm
  have apc390:=fun (q417 q418 q419:G)=>by
    exact (((apc347 q418 q419 q417).symm).trans ((((cg (fun t => (q419 ◇ ((q418 ◇ q418) ◇ q418)) ◇ t) (apc5 q418 q418 q417)).symm).trans (apc347 q418 q419 (q418 ◇ q417))).trans (apc269 q417 q418 q419))).symm
  have apc391:=fun (q348 q349 q417 q418 q419:G)=>by
    exact (((apc390 q348 q349 q348).symm).trans (apc271 q348 q349)).symm
  have apc392:=fun (q345 q346 q347 q417 q418 q419:G)=>by
    exact (apc269 q345 q346 q347).trans (apc390 q345 q346 q347)
  have apc393:=fun (q420 q421:G)=>by
    exact (((apc98 q421 q420 q421).symm).trans (((apc390 (q421 ◇ q420) q421 q420).symm).trans ((h (q421 ◇ q420) (q421 ◇ q421) q421).symm))).symm
  have apc394:=fun (q417 q418 q419 q190 q191 q192:G)=>by
    exact (apc122 q190 q191 q192).trans (apc390 q192 q190 q191)
  have apc396:=fun (q422 q423:G)=>by
    exact (((cg (fun t => t ◇ q423) (apc6 q422 q423)).symm).trans (apc393 (q423 ◇ q422) q423)).trans (cg (fun t => t ◇ q423) (apc225 ((q423 ◇ q422) ◇ ((q423 ◇ q423) ◇ q423)) ((q423 ◇ q422) ◇ ((q423 ◇ q423) ◇ q423)) q423 q422))
  have apc399:=fun (q424 q425 q426:G)=>by
    exact (((cg (fun t => t ◇ (q426 ◇ q425)) ((h (q426 ◇ q426) q426 q424).symm)).symm).trans (apc392 q425 q426 (q424 ◇ (q426 ◇ q426)) q424 q424 q424)).trans ((cg (fun t => t ◇ q425) (apc250 q424 q426 q426)).trans (cg (fun t => t ◇ q425) (apc18 q424 q426)))
  have apc400:=fun (q427 q428:G)=>by
    exact (((apc399 q427 q427 q428).symm).trans ((h q427 ((q428 ◇ q428) ◇ q428) q428).symm)).symm
  have apc401:=fun (q420 q421 q427 q428:G)=>by
    exact ((apc393 q420 q421).trans (apc400 q420 q421)).symm
  have apc408:=fun (q280 q281 q282 q283 q295 q284:G)=>by
    exact (apc198 q280 q281 q282 q283 q284).trans (apc202 q281 q280 q283 q282 q284)
  have apc411:=fun (q429 q430 q431:G)=>by
    exact (((apc326 q430 q429 q431 q431 (q429 ◇ q431)).symm).trans (((apc408 q431 q429 q431 q431 q429 q430).symm).trans (apc5 ((q429 ◇ q431) ◇ q430) q431 (q429 ◇ q431)))).symm
  have apc412:=fun (q432 q433 q434:G)=>by
    exact ((apc180 q434 q433 q434 q432).symm).trans ((((cg (fun t => t ◇ (q433 ◇ (q434 ◇ q434))) (apc18 q432 q434)).symm).trans (apc408 q434 q434 q432 q433 q432 q434)).trans ((apc394 ((((q434 ◇ q434) ◇ q434) ◇ q432) ◇ ((q434 ◇ q433) ◇ q434)) ((((q434 ◇ q434) ◇ q434) ◇ q432) ◇ ((q434 ◇ q433) ◇ q434)) ((((q434 ◇ q434) ◇ q434) ◇ q432) ◇ ((q434 ◇ q433) ◇ q434)) q434 q432 (q434 ◇ q433)).trans (apc392 q433 q434 q432 (((q434 ◇ (q434 ◇ q434)) ◇ q432) ◇ (q434 ◇ q433)) (((q434 ◇ (q434 ◇ q434)) ◇ q432) ◇ (q434 ◇ q433)) (((q434 ◇ (q434 ◇ q434)) ◇ q432) ◇ (q434 ◇ q433)))))
  have apc414:=fun (q435 q436:G)=>by
    exact (((apc98 q436 q435 q436).symm).trans ((((apc412 q435 (q436 ◇ q435) q436).symm).trans ((h (q436 ◇ q435) (q436 ◇ q436) (q436 ◇ q436)).symm)).trans (apc5 (q436 ◇ q435) q436 q436))).symm
  have apc415:=fun (q364 q365 q435 q436:G)=>by
    exact (apc285 q364 q365).trans (apc414 q364 q365)
  have apc430:=fun (q437 q438:G)=>by
    exact (((apc415 (q437 ◇ q438) q437 ((q437 ◇ ((q437 ◇ q437) ◇ (q437 ◇ q438))) ◇ q437) ((q437 ◇ ((q437 ◇ q437) ◇ (q437 ◇ q438))) ◇ q437)).trans (cg (fun t => t ◇ q437) (apc225 ((q437 ◇ q438) ◇ ((q437 ◇ q437) ◇ q437)) ((q437 ◇ q438) ◇ ((q437 ◇ q437) ◇ q437)) q437 q438))).symm).trans ((((apc284 q437 (q437 ◇ q438)).symm).trans (apc4 q437 q437 ((q437 ◇ q437) ◇ q437) q438)).trans ((apc140 q437 q438 (q437 ◇ q437)).trans (apc284 q437 q438)))
  have apc441:=fun (q439 q440 q441:G)=>by
    exact ((cg (fun t => (q441 ◇ q440) ◇ t) (apc401 q439 q440 (((q440 ◇ (q440 ◇ q440)) ◇ q439) ◇ q439) (((q440 ◇ (q440 ◇ q440)) ◇ q439) ◇ q439))).symm).trans (((cg (fun t => (q441 ◇ q440) ◇ t) (apc391 q439 q440 q439 q439 q439)).symm).trans ((h q440 q441 (q439 ◇ (q440 ◇ (q440 ◇ q440)))).symm))
  have apc442:=fun (q442 q443 q444:G)=>by
    exact (((apc441 q442 q443 q444).symm).trans ((h q443 q444 ((q443 ◇ q442) ◇ (q443 ◇ q443))).symm)).symm
  have apc454:=fun (q445 q446 q447 q448 q449:G)=>by
    exact (((cg (fun t => t ◇ ((q447 ◇ q446) ◇ (q448 ◇ q446))) (cg (fun t => t ◇ q449) ((h q446 q445 q448).symm))).symm).trans (apc13 q446 q447 q448 (q445 ◇ q446) q449)).trans (apc320 q448 q449 q445 q446 ((q446 ◇ q447) ◇ q448))
  have apc457:=fun (q450 q451 q452 q453 q454:G)=>by
    exact (((apc1 (q452 ◇ q451) q450 q453 q454).symm).trans (((cg (fun t => (q454 ◇ (q453 ◇ (q452 ◇ q451))) ◇ t) (cg (fun t => t ◇ q453) ((h q452 q451 q450).symm))).symm).trans (apc65 q451 q452 (q450 ◇ q452) q453 q454))).symm
  have apc458:=fun (q455 q456 q457 q458:G)=>by
    exact ((apc457 q455 q456 q458 q457 q458).symm).trans ((h q458 (q457 ◇ (q458 ◇ q456)) (q456 ◇ (q455 ◇ q458))).symm)
  have apc459:=fun (q459 q460 q461 q462:G)=>by
    exact (((cg (fun t => t ◇ (q460 ◇ (q462 ◇ q461))) (cg (fun t => t ◇ q462) ((h q461 q459 q462).symm))).symm).trans (apc458 q460 q461 (q459 ◇ q461) q462)).trans (apc327 ((q462 ◇ ((q459 ◇ q461) ◇ (q462 ◇ q461))) ◇ (q461 ◇ (q460 ◇ q462))) ((q462 ◇ ((q459 ◇ q461) ◇ (q462 ◇ q461))) ◇ (q461 ◇ (q460 ◇ q462))) ((q462 ◇ ((q459 ◇ q461) ◇ (q462 ◇ q461))) ◇ (q461 ◇ (q460 ◇ q462))) ((q462 ◇ ((q459 ◇ q461) ◇ (q462 ◇ q461))) ◇ (q461 ◇ (q460 ◇ q462))) ((q462 ◇ ((q459 ◇ q461) ◇ (q462 ◇ q461))) ◇ (q461 ◇ (q460 ◇ q462))) q462 q459 q461 q462 (q461 ◇ (q460 ◇ q462)))
  have apc474:=fun (q463 q464 q465:G)=>by
    exact ((apc21 q464 q464 q463 q465).symm).trans ((((cg (fun t => t ◇ ((q463 ◇ q464) ◇ q464)) (cg (fun t => q465 ◇ t) ((h q464 q463 q464).symm))).symm).trans (apc20 q464 (q463 ◇ q464) q465)).trans (apc411 q463 q465 q464))
  have apc477:=fun (q466 q467:G)=>by
    exact (((apc327 ((q467 ◇ ((q467 ◇ q466) ◇ (q466 ◇ q466))) ◇ (q466 ◇ q467)) ((q467 ◇ ((q467 ◇ q466) ◇ (q466 ◇ q466))) ◇ (q466 ◇ q467)) ((q467 ◇ ((q467 ◇ q466) ◇ (q466 ◇ q466))) ◇ (q466 ◇ q467)) ((q467 ◇ ((q467 ◇ q466) ◇ (q466 ◇ q466))) ◇ (q466 ◇ q467)) ((q467 ◇ ((q467 ◇ q466) ◇ (q466 ◇ q466))) ◇ (q466 ◇ q467)) q466 q467 q466 q467 (q466 ◇ q467)).symm).trans (((apc474 q466 q467 (q466 ◇ q466)).symm).trans (apc5 ((q467 ◇ q466) ◇ q467) q466 q467))).symm
  have apc486:=fun (q468 q469 q470:G)=>by
    exact ((cg (fun t => (q470 ◇ q469) ◇ t) (apc69 q468 q469)).symm).trans ((h q469 q470 ((q469 ◇ (q468 ◇ q469)) ◇ q469)).symm)
  have apc487:=fun (q471 q472 q473:G)=>by
    exact ((apc486 q471 q472 q473).symm).trans ((h q472 q473 ((q472 ◇ q471) ◇ q472)).symm)
  have apc488:=fun (q474 q475:G)=>by
    exact ((apc487 q474 q475 q475).symm).trans ((h q475 q475 (q475 ◇ (q474 ◇ q475))).symm)
  have apc489:=fun (q476 q477:G)=>by
    exact ((apc488 q476 q477).symm).trans ((h q477 q477 (q477 ◇ q476)).symm)
  have apc491:=fun (q474 q475 q476 q477:G)=>by
    exact (apc488 q474 q475).trans (apc489 q474 q475)
  have apc502:=fun (q311 q312 q313 q100 q101 q102:G)=>by
    exact ((((cg (fun t => t ◇ (q102 ◇ q101)) (apc226 q102 q100 ((q100 ◇ q102) ◇ ((q102 ◇ q102) ◇ q102)) ((q100 ◇ q102) ◇ ((q102 ◇ q102) ◇ q102)))).trans (apc5 (q102 ◇ q100) q102 q101)).symm).trans ((((apc219 q100 q102 (q102 ◇ q101)).symm).trans (apc61 q100 q101 q102)).trans (apc326 q100 q102 q102 q102 q101))).symm
  have apc503:=fun (q478 q479 q480:G)=>by
    exact ((((cg (fun t => t ◇ ((q479 ◇ q480) ◇ q480)) ((h q480 q480 q478).symm)).symm).trans (apc251 q479 q480 (q478 ◇ q480))).trans (apc10 q478 q480 ((q480 ◇ q479) ◇ q480))).symm
  have apc507:=fun (q481 q482 q483:G)=>by
    exact (((apc441 q481 q482 q483).symm).trans (((cg (fun t => (q483 ◇ q482) ◇ t) (apc396 q481 q482)).symm).trans ((h q482 q483 (((q482 ◇ q482) ◇ q481) ◇ q482)).symm))).symm
  have apc508:=fun (q484 q485:G)=>by
    exact ((apc507 q484 q485 q485).symm).trans ((h q485 q485 ((q485 ◇ q485) ◇ q484)).symm)
  have apc510:=fun (q486 q487:G)=>by
    exact (((cg (fun t => (q487 ◇ q487) ◇ t) (apc103 q487 q486)).symm).trans (apc508 (q486 ◇ q487) q487)).trans (apc236 q486 q487 q487)
  have apc520:=fun (q488 q489 q490 q491:G)=>by
    exact ((apc0 q490 q490 q491 (q489 ◇ (q491 ◇ q488))).symm).trans (((cg (fun t => ((q490 ◇ q490) ◇ q491) ◇ t) (apc4 q490 q491 q488 q489)).symm).trans (apc84 q490 ((q491 ◇ q489) ◇ q488) q491))
  have apc521:=fun (q492 q493 q494 q495:G)=>by
    exact ((cg (fun t => t ◇ (q493 ◇ (q495 ◇ q492))) ((h q494 q495 q494).symm)).symm).trans (apc520 q492 q493 q494 q495)
  have apc550:=fun (q496 q497 q498 q499 q500:G)=>by
    exact (((cg (fun t => t ◇ (q499 ◇ q500)) (apc12 q496 q497 q498 q500)).symm).trans (apc4 q499 q500 (q498 ◇ q497) (q498 ◇ (q496 ◇ q500)))).symm
  have apc551:=fun (q501 q502 q503:G)=>by
    exact (((cg (fun t => t ◇ (q501 ◇ q503)) ((h (q502 ◇ q501) q502 q501).symm)).symm).trans (apc550 q502 q501 q502 q503 q501)).symm
  have apc552:=fun (q504 q505 q506:G)=>by
    exact (((cg (fun t => t ◇ (q506 ◇ q504)) ((h q505 (q504 ◇ q505) q504).symm)).symm).trans (apc551 q504 q505 q506)).symm
  have apc553:=fun (q507 q508:G)=>by
    exact ((apc552 q508 q507 q508).symm).trans ((h q508 ((q507 ◇ q508) ◇ q507) q508).symm)
  have apc554:=fun (q509 q510:G)=>by
    exact ((apc553 q509 q510).symm).trans ((h q510 (q509 ◇ (q510 ◇ q509)) q510).symm)
  have apc555:=fun (q511 q512 q513 q514:G)=>by
    exact (((cg (fun t => t ◇ (q514 ◇ q513)) (apc5 q512 q514 (q512 ◇ q511))).symm).trans (apc550 q514 q511 q512 q513 q514)).symm
  have apc556:=fun (q515 q516:G)=>by
    exact ((((apc321 q515 q516 q515 (q516 ◇ q515) (((q516 ◇ (q516 ◇ q515)) ◇ (q515 ◇ q515)) ◇ (q516 ◇ q515)) (((q516 ◇ (q516 ◇ q515)) ◇ (q515 ◇ q515)) ◇ (q516 ◇ q515)) (((q516 ◇ (q516 ◇ q515)) ◇ (q515 ◇ q515)) ◇ (q516 ◇ q515)) (((q516 ◇ (q516 ◇ q515)) ◇ (q515 ◇ q515)) ◇ (q516 ◇ q515)) (((q516 ◇ (q516 ◇ q515)) ◇ (q515 ◇ q515)) ◇ (q516 ◇ q515))).trans (apc326 q516 q515 q516 q515 q516)).symm).trans ((((apc555 q515 q515 q515 q516).symm).trans (apc5 ((q516 ◇ q515) ◇ q516) q515 q516)).trans (apc477 q515 q516))).symm
  have apc557:=fun (q466 q467 q515 q516:G)=>by
    exact (apc477 q466 q467).trans (apc556 q466 q467)
  have apc567:=fun (q517 q518 q519 q520:G)=>by
    exact (((apc40 q520 q519 q518 (q520 ◇ q517)).symm).trans (((cg (fun t => ((q519 ◇ (q519 ◇ q520)) ◇ q518) ◇ t) ((h q520 q517 (q519 ◇ q518)).symm)).symm).trans (apc191 q518 q519 q520 (q517 ◇ q520)))).symm
  have apc568:=fun (q521 q522 q523 q524:G)=>by
    exact (((apc3 q521 (q522 ◇ q523) q523 q524).symm).trans (((cg (fun t => (((q522 ◇ q523) ◇ q523) ◇ q524) ◇ t) (cg (fun t => t ◇ q524) ((h q522 q523 q521).symm))).symm).trans (apc200 q522 q523 q524 (q521 ◇ q522)))).symm
  have apc569:=fun (q525 q526 q527:G)=>by
    exact (((cg (fun t => t ◇ (q525 ◇ q527)) ((h q527 q526 (q526 ◇ q527)).symm)).symm).trans (apc568 q525 q527 q526 q527)).symm
  have apc582:=fun (q528 q529 q530 q531:G)=>by
    exact (((apc0 q529 (q529 ◇ q530) (q529 ◇ q528) q531).trans (cg (fun t => t ◇ q531) (apc3 q530 q529 q528 q529))).symm).trans ((((cg (fun t => ((q529 ◇ (q529 ◇ q530)) ◇ (q529 ◇ q528)) ◇ t) (cg (fun t => q531 ◇ t) ((h q529 q528 q529).symm))).symm).trans (apc280 q528 q529 q529 q530 q531)).trans (apc320 q528 q530 q529 q529 q531))
  have apc588:=fun (q532 q533 q534 q535 q536:G)=>by
    exact ((cg (fun t => (q536 ◇ q535) ◇ t) (apc582 q532 q533 q534 q535)).symm).trans ((h q535 q536 (((q533 ◇ q533) ◇ q532) ◇ (q534 ◇ q533))).symm)
  have apc589:=fun (q537 q538 q539 q540 q541:G)=>by
    exact ((apc588 q537 q538 q539 q540 q541).symm).trans ((h q540 q541 (((q538 ◇ q538) ◇ q537) ◇ q539)).symm)
  have apc595:=fun (q542 q543 q544 q545:G)=>by
    exact ((cg (fun t => ((q544 ◇ q545) ◇ (q544 ◇ q542)) ◇ t) ((h (q544 ◇ q542) q543 q544).symm)).symm).trans (apc286 q542 q543 q544 q545 (q544 ◇ q542))
  have apc596:=fun (q546 q547 q548:G)=>by
    exact (((cg (fun t => t ◇ (((q548 ◇ q546) ◇ q547) ◇ q548)) ((h q546 q548 q548).symm)).symm).trans (apc595 q546 q547 q548 q546)).trans (apc3 q547 q548 (q548 ◇ q546) q546)
  have apc597:=fun (q549 q550 q551:G)=>by
    exact ((apc596 q549 q550 q551).symm).trans ((h q551 (q549 ◇ q551) ((q551 ◇ q549) ◇ q550)).symm)
  have apc598:=fun (q552 q553 q554:G)=>by
    exact (((cg (fun t => t ◇ (q553 ◇ q554)) ((h q552 q554 q554).symm)).symm).trans (apc597 q552 q553 q554)).symm
  have apc601:=fun (q555 q556 q557:G)=>by
    exact (((cg (fun t => (q557 ◇ (q556 ◇ q557)) ◇ t) ((h q556 q557 q555).symm)).symm).trans (apc598 q556 (q555 ◇ q556) q557)).symm
  have apc603:=fun (q558 q559 q560:G)=>by
    exact ((apc601 q558 q559 q560).symm).trans ((h q560 (q559 ◇ q560) (q558 ◇ q559)).symm)
  have apc605:=fun (q561 q562:G)=>by
    exact ((apc603 q561 q561 q562).symm).trans (((apc603 (q561 ◇ q562) q561 q562).symm).trans ((h (q561 ◇ q562) q562 (q561 ◇ q562)).symm))
  have apc610:=fun (q563 q564 q565 q566:G)=>by
    exact (((apc326 q566 q564 q565 q566 (q565 ◇ q563)).symm).trans (((cg (fun t => (((q565 ◇ q564) ◇ q566) ◇ q566) ◇ t) ((h q565 q563 q566).symm)).symm).trans (apc459 q564 (q563 ◇ q565) q565 q566))).symm
  have apc611:=fun (q567 q568:G)=>by
    exact ((apc610 q567 q567 q567 q568).symm).trans ((h ((q567 ◇ q567) ◇ q568) q568 q567).symm)
  have apc612:=fun (q569 q570 q571:G)=>by
    exact (((apc80 q569 q571 (q570 ◇ q571)).symm).trans (apc4 q570 q571 (q571 ◇ (q569 ◇ q571)) q571)).trans (apc199 q569 q571 (q571 ◇ q570))
  have apc614:=fun (q572 q573 q574:G)=>by
    exact ((cg (fun t => t ◇ (q574 ◇ q573)) (apc414 q572 q573)).symm).trans ((((cg (fun t => t ◇ (q574 ◇ q573)) (apc285 q572 q573)).symm).trans ((h q573 (q573 ◇ ((q573 ◇ q573) ◇ q572)) q574).symm)).trans (apc49 q572 q573 q574))
  have apc630:=fun (q575 q576 q577 q578 q579:G)=>by
    exact (((cg (fun t => t ◇ ((q578 ◇ q577) ◇ (q579 ◇ q577))) ((h q579 (q577 ◇ q576) q575).symm)).symm).trans (apc454 q576 q577 q578 q579 (q575 ◇ q579))).trans ((apc9 (q577 ◇ q578) q579 q575 (q577 ◇ q576) ((((q577 ◇ q576) ◇ q579) ◇ (q575 ◇ q579)) ◇ ((q577 ◇ q578) ◇ q579)) ((((q577 ◇ q576) ◇ q579) ◇ (q575 ◇ q579)) ◇ ((q577 ◇ q578) ◇ q579)) ((((q577 ◇ q576) ◇ q579) ◇ (q575 ◇ q579)) ◇ ((q577 ◇ q578) ◇ q579)) ((((q577 ◇ q576) ◇ q579) ◇ (q575 ◇ q579)) ◇ ((q577 ◇ q578) ◇ q579))).trans (apc4 (q577 ◇ q578) q579 q575 (q577 ◇ q576)))
  have apc653:=fun (q386 q580 q387 q388 q389 q581:G)=>by
    exact ((cg (fun t => (q581 ◇ q389) ◇ t) (apc320 q386 q580 q387 q388 q389)).symm).trans ((h q389 q581 (((q387 ◇ q388) ◇ (q386 ◇ q388)) ◇ q580)).symm)
  have apc659:=fun (q582 q583 q584 q585 q586 q587:G)=>by
    exact ((apc653 q582 q583 q584 q585 q586 q587).symm).trans ((h q586 q587 (((q585 ◇ q584) ◇ q582) ◇ q583)).symm)
  have apc660:=fun (q588 q589 q590 q591 q592:G)=>by
    exact ((apc659 q588 q591 q589 q590 q592 q591).symm).trans ((h q591 q592 ((q589 ◇ q590) ◇ (q588 ◇ q590))).symm)
  have apc661:=fun (q593 q594 q595 q596 q597:G)=>by
    exact ((apc660 q593 q594 q595 q596 q597).symm).trans ((h q596 q597 ((q595 ◇ q594) ◇ q593)).symm)
  have apc662:=fun (q588 q589 q590 q591 q592 q593 q594 q595 q596 q597:G)=>by
    exact (apc660 q588 q589 q590 q591 q592).trans (apc661 q588 q589 q590 q591 q592)
  have apc669:=fun (q598 q599 q600:G)=>by
    exact (((cg (fun t => t ◇ q600) (apc326 q599 q600 q600 q598 q599)).symm).trans (((apc19 (q600 ◇ q600) q598 q599 q600).symm).trans (apc5 (q599 ◇ q598) q600 (((q600 ◇ q600) ◇ q599) ◇ q598)))).symm
  have apc686:=fun (q601 q602 q603:G)=>by
    exact ((((apc62 q601 q602 q602 q603).trans (apc66 q601 q602 q603)).symm).trans (((cg (fun t => (q603 ◇ q602) ◇ t) (apc290 q601 q602)).symm).trans ((h q602 q603 ((q601 ◇ (q602 ◇ q602)) ◇ q602)).symm))).symm
  have apc687:=fun (q604 q605:G)=>by
    exact ((apc686 q604 q605 q605).symm).trans ((h q605 q605 (q604 ◇ (q605 ◇ q605))).symm)
  have apc688:=fun (q606 q607 q608:G)=>by
    exact (((cg (fun t => (q607 ◇ q608) ◇ t) (cg (fun t => t ◇ q607) ((h q607 q606 q607).symm))).symm).trans (apc686 (q606 ◇ q607) q607 q608)).trans (apc66 q606 q607 q608)
  have apc689:=fun (q609 q610:G)=>by
    exact ((apc687 q609 q610).symm).trans ((((apc688 q609 q610 q610).symm).trans ((h q610 q610 ((q610 ◇ q609) ◇ q610)).symm)).trans (apc491 q609 q610 ((q610 ◇ q610) ◇ ((q610 ◇ q609) ◇ q610)) ((q610 ◇ q610) ◇ ((q610 ◇ q609) ◇ q610))))
  have apc690:=fun (q604 q605 q609 q610:G)=>by
    exact (apc687 q604 q605).trans (apc689 q604 q605)
  have apc691:=fun (q486 q487 q609 q610:G)=>by
    exact (((apc690 q486 q487 ((q487 ◇ q487) ◇ (q487 ◇ (q487 ◇ q486))) ((q487 ◇ q487) ◇ (q487 ◇ (q487 ◇ q486)))).symm).trans (((apc689 (q487 ◇ q486) q487).symm).trans (apc510 q486 q487))).symm
  have apc695:=fun (q611 q612 q613:G)=>by
    exact (((cg (fun t => (q612 ◇ q613) ◇ t) (apc6 q611 q612)).symm).trans (apc442 (q612 ◇ q611) q612 q613)).trans (cg (fun t => (q612 ◇ q613) ◇ t) (apc224 q612 q611))
  have apc699:=fun (q614 q615 q616:G)=>by
    exact ((((apc203 ((((q615 ◇ q615) ◇ q614) ◇ q615) ◇ ((q615 ◇ q616) ◇ q615)) ((((q615 ◇ q615) ◇ q614) ◇ q615) ◇ ((q615 ◇ q616) ◇ q615)) ((((q615 ◇ q615) ◇ q614) ◇ q615) ◇ ((q615 ◇ q616) ◇ q615)) ((((q615 ◇ q615) ◇ q614) ◇ q615) ◇ ((q615 ◇ q616) ◇ q615)) ((((q615 ◇ q615) ◇ q614) ◇ q615) ◇ ((q615 ◇ q616) ◇ q615)) q615 q615 q614 q616).trans (cg (fun t => t ◇ q616) (apc691 q614 q615 ((q615 ◇ q615) ◇ ((q615 ◇ q615) ◇ q614)) ((q615 ◇ q615) ◇ ((q615 ◇ q615) ◇ q614))))).symm).trans ((((cg (fun t => t ◇ ((q615 ◇ q616) ◇ q615)) (apc15 q614 q615)).symm).trans (apc1 q615 q616 q615 ((q615 ◇ q615) ◇ q614))).trans (cg (fun t => t ◇ (q616 ◇ q615)) (apc691 q614 q615 ((q615 ◇ q615) ◇ ((q615 ◇ q615) ◇ q614)) ((q615 ◇ q615) ◇ ((q615 ◇ q615) ◇ q614)))))).symm
  have apc701:=fun (q614 q615 q616 q569 q570 q571:G)=>by
    exact (((apc699 q569 q571 q570).symm).trans (apc612 q569 q570 q571)).symm
  have apc703:=fun (q617 q618 q619:G)=>by
    exact ((((apc180 q619 q617 q619 q618).trans (apc412 q618 q617 q619)).symm).trans (((cg (fun t => t ◇ (q617 ◇ (q619 ◇ q619))) (apc87 q618 q619)).symm).trans (apc4 q617 (q619 ◇ q619) q618 q619))).symm
  have apc706:=fun (q620 q621 q622:G)=>by
    exact (((apc4 (q620 ◇ q621) q622 q620 (q622 ◇ q622)).trans (apc390 (q620 ◇ q621) q622 q620)).symm).trans ((((cg (fun t => t ◇ ((q620 ◇ q621) ◇ q622)) (apc89 q622 q620)).symm).trans (apc1 q620 q621 q622 ((q622 ◇ q622) ◇ q622))).trans (cg (fun t => t ◇ (q621 ◇ q620)) (apc225 ((q622 ◇ q620) ◇ ((q622 ◇ q622) ◇ q622)) ((q622 ◇ q620) ◇ ((q622 ◇ q622) ◇ q622)) q622 q620)))
  have apc754:=fun (q623 q624 q625:G)=>by
    exact (((cg (fun t => (q625 ◇ (q624 ◇ (q624 ◇ q623))) ◇ t) (apc5 q624 q624 q623)).symm).trans (apc41 q624 q624 (q624 ◇ q623) q625)).trans (apc282 q624 q625 (q624 ◇ q623))
  have apc759:=fun (q626 q627 q628:G)=>by
    exact (((cg (fun t => t ◇ (q628 ◇ ((q626 ◇ q626) ◇ q627))) (apc109 q626 q627)).symm).trans ((h ((q626 ◇ q626) ◇ q627) (q626 ◇ (q626 ◇ q626)) q628).symm)).trans (cg (fun t => t ◇ q628) (apc248 q626 q627))
  have apc760:=fun (q629 q630 q631:G)=>by
    exact (((((apc180 q630 (q631 ◇ q629) q630 q631).trans (apc412 q631 (q631 ◇ q629) q630)).trans (apc706 q631 q629 q630)).symm).trans (((cg (fun t => ((q630 ◇ (q630 ◇ q630)) ◇ q631) ◇ t) ((h q631 q629 (q630 ◇ q630)).symm)).symm).trans (apc759 q630 q631 (q629 ◇ q631)))).symm
  have apc767:=fun (q632 q633 q634 q635:G)=>by
    exact (((cg (fun t => t ◇ (q634 ◇ (q633 ◇ q635))) (cg (fun t => t ◇ q635) ((h q633 q635 q632).symm))).symm).trans (apc273 q633 (q632 ◇ q633) q634 q635)).symm
  have apc768:=fun (q636 q637 q638:G)=>by
    exact (((cg (fun t => t ◇ ((q636 ◇ q638) ◇ q637)) (apc5 q638 q636 q638)).symm).trans (apc767 q636 q636 q637 q638)).trans (apc569 q637 q638 q636)
  have apc769:=fun (q639 q640:G)=>by
    exact (((apc768 q639 q640 q640).symm).trans ((h q640 (q639 ◇ (q639 ◇ q640)) (q639 ◇ q640)).symm)).trans (apc12 q639 q640 q639 q640)
  have apc792:=fun (q641 q642:G)=>by
    exact ((cg (fun t => t ◇ q642) (apc396 q641 q642)).symm).trans ((((cg (fun t => t ◇ q642) (cg (fun t => t ◇ q642) (apc6 q641 q642))).symm).trans (apc290 (q642 ◇ (q642 ◇ q641)) q642)).trans ((((cg (fun t => t ◇ (q642 ◇ q642)) (apc414 q641 q642)).trans (apc614 q641 q642 q642)).trans (apc326 q641 q642 q642 q642 q642)).trans (apc415 q641 q642 ((q642 ◇ ((q642 ◇ q642) ◇ q641)) ◇ q642) ((q642 ◇ ((q642 ◇ q642) ◇ q641)) ◇ q642))))
  have apc802:=fun (q643 q644 q645:G)=>by
    exact (((apc4 q645 q644 q644 (q643 ◇ (q644 ◇ q643))).trans (cg (fun t => t ◇ (q644 ◇ q645)) (apc605 q644 q643))).symm).trans (((cg (fun t => t ◇ (q645 ◇ q644)) (apc554 q643 q644)).symm).trans ((h q644 (q644 ◇ ((q643 ◇ q644) ◇ q643)) q645).symm))
  have apc803:=fun (q646 q647 q648:G)=>by
    exact (((cg (fun t => t ◇ (q647 ◇ q648)) ((h q646 (q647 ◇ q646) q647).symm)).symm).trans (apc802 q646 q647 q648)).symm
  have apc804:=fun (q646 q647 q648 q466 q467 q515 q516:G)=>by
    exact ((((apc4 q466 q467 q466 (q466 ◇ q467)).trans (apc769 q466 q467)).symm).trans (((apc803 q467 q466 q467).symm).trans (apc557 q466 q467 q466 q466))).symm
  have apc869:=fun (q649 q650 q651 q652:G)=>by
    exact ((cg (fun t => (q651 ◇ q652) ◇ t) (apc5 (q649 ◇ q649) q650 q649)).symm).trans (apc589 (q650 ◇ q650) q649 q650 q651 q652)
  have apc870:=fun (q653 q654 q655:G)=>by
    exact ((apc869 q654 q653 q655 q654).symm).trans ((h q654 q655 (q653 ◇ (q653 ◇ (q654 ◇ q654)))).symm)
  have apc873:=fun (q656 q657:G)=>by
    exact (((((apc754 q656 q657 q657).trans (apc5 (q657 ◇ q656) q657 (q657 ◇ q657))).trans (apc6 (q657 ◇ q656) q657)).symm).trans (((cg (fun t => (q657 ◇ (q657 ◇ (q657 ◇ q656))) ◇ t) (apc87 q656 q657)).symm).trans (apc669 q656 q657 q657))).symm
  have apc874:=fun (q658 q659:G)=>by
    exact ((apc792 q658 q659).symm).trans ((((cg (fun t => t ◇ q659) (cg (fun t => t ◇ q659) ((h q659 q658 (q659 ◇ q659)).symm))).symm).trans (apc873 (q658 ◇ q659) q659)).trans (cg (fun t => t ◇ q659) (apc489 q658 q659)))
  have apc880:=fun (q660 q661:G)=>by
    exact ((((cg (fun t => t ◇ q661) ((h q661 q660 (q661 ◇ q661)).symm)).symm).trans (apc874 (q660 ◇ q661) q661)).trans (cg (fun t => t ◇ q661) (apc489 q660 q661))).symm
  have apc896:=fun (q662 q663 q664 q665:G)=>by
    exact ((apc1 q662 (q662 ◇ (q663 ◇ q664)) q663 q665).symm).trans (((cg (fun t => (q665 ◇ (q663 ◇ q662)) ◇ t) (apc20 q662 q663 q664)).symm).trans ((h (q663 ◇ q662) q665 (q664 ◇ (q663 ◇ (q662 ◇ q662)))).symm))
  have apc897:=fun (q666 q667 q668:G)=>by
    exact ((apc896 q668 q666 q667 q668).symm).trans ((h q668 (q666 ◇ q668) (q668 ◇ (q666 ◇ q667))).symm)
  have apc899:=fun (q669 q670 q671 q672:G)=>by
    exact (((cg (fun t => t ◇ (q671 ◇ q672)) (apc20 q669 q670 q672)).symm).trans (apc4 q671 q672 (q670 ◇ q669) (q670 ◇ (q669 ◇ q669)))).symm
  have apc900:=fun (q673 q674 q675:G)=>by
    exact (((cg (fun t => t ◇ (q675 ◇ q674)) ((h (q673 ◇ q673) q673 q675).symm)).symm).trans (apc899 q673 q673 q674 q675)).symm
  have apc929:=fun (q676 q677 q678:G)=>by
    exact ((apc900 q677 q676 q678).symm).trans ((((cg (fun t => t ◇ (q676 ◇ q678)) (apc5 (q677 ◇ q678) q677 q677)).symm).trans (apc567 q676 (q677 ◇ q677) q677 q678)).trans (((cg (fun t => t ◇ (q678 ◇ q676)) (apc250 q678 q677 q677)).trans (cg (fun t => t ◇ (q678 ◇ q676)) (apc18 q678 q677))).trans (apc706 q678 q676 q677)))
  have apc940:=fun (q679 q680 q681:G)=>by
    exact ((((cg (fun t => (q681 ◇ q680) ◇ t) (apc880 q679 q680)).trans (apc662 (q680 ◇ q680) q679 q680 q680 q681 ((q681 ◇ q680) ◇ (((q680 ◇ q679) ◇ (q680 ◇ q680)) ◇ q680)) ((q681 ◇ q680) ◇ (((q680 ◇ q679) ◇ (q680 ◇ q680)) ◇ q680)) ((q681 ◇ q680) ◇ (((q680 ◇ q679) ◇ (q680 ◇ q680)) ◇ q680)) ((q681 ◇ q680) ◇ (((q680 ◇ q679) ◇ (q680 ◇ q680)) ◇ q680)) ((q681 ◇ q680) ◇ (((q680 ◇ q679) ◇ (q680 ◇ q680)) ◇ q680)))).symm).trans ((((cg (fun t => (q681 ◇ q680) ◇ t) (apc132 q679 q679 q679 q679 q679 q680)).symm).trans ((h q680 q681 ((q680 ◇ (q680 ◇ q680)) ◇ q679)).symm)).trans (apc345 q679 q680 q681))).symm
  have apc941:=fun (q679 q680 q681 q404 q405:G)=>by
    exact ((apc940 q404 q405 q404).symm).trans (apc343 q404 q405)
  have apc942:=fun (q682 q683:G)=>by
    exact (((cg (fun t => ((q683 ◇ q682) ◇ (q683 ◇ q683)) ◇ t) (cg (fun t => t ◇ ((q683 ◇ q682) ◇ (q683 ◇ q682))) (apc941 ((q683 ◇ q682) ◇ ((q683 ◇ q682) ◇ (q683 ◇ q683))) ((q683 ◇ q682) ◇ ((q683 ◇ q682) ◇ (q683 ◇ q683))) ((q683 ◇ q682) ◇ ((q683 ◇ q682) ◇ (q683 ◇ q683))) q682 q683))).trans (cg (fun t => ((q683 ◇ q682) ◇ (q683 ◇ q683)) ◇ t) (apc661 q683 q683 q682 (q683 ◇ q682) (q683 ◇ q683)))).symm).trans ((((cg (fun t => t ◇ (((q683 ◇ q682) ◇ ((q683 ◇ q682) ◇ (q683 ◇ q683))) ◇ ((q683 ◇ q682) ◇ (q683 ◇ q682)))) (apc941 q682 q682 q682 q682 q683)).symm).trans (apc941 q682 q682 q682 ((q683 ◇ q682) ◇ (q683 ◇ q683)) (q683 ◇ q682))).trans ((cg (fun t => t ◇ ((q683 ◇ q682) ◇ (q683 ◇ q682))) (apc941 ((q683 ◇ q682) ◇ ((q683 ◇ q682) ◇ (q683 ◇ q683))) ((q683 ◇ q682) ◇ ((q683 ◇ q682) ◇ (q683 ◇ q683))) ((q683 ◇ q682) ◇ ((q683 ◇ q682) ◇ (q683 ◇ q683))) q682 q683)).trans (apc661 q683 q683 q682 (q683 ◇ q682) (q683 ◇ q683))))
  have apc946:=fun (q684 q685 q686:G)=>by
    exact (((cg (fun t => ((q684 ◇ q685) ◇ q686) ◇ t) (apc333 q686 q684 q685 (q685 ◇ q684) q684)).trans (cg (fun t => ((q684 ◇ q685) ◇ q686) ◇ t) (apc661 q685 q685 q684 (q684 ◇ q685) q686))).symm).trans ((((cg (fun t => t ◇ (((q685 ◇ q684) ◇ (q686 ◇ q684)) ◇ ((q685 ◇ q684) ◇ (q685 ◇ q684)))) ((h q684 q685 q686).symm)).symm).trans (apc941 q684 q684 q684 (q686 ◇ q684) (q685 ◇ q684))).trans ((apc333 q686 q684 q685 (q685 ◇ q684) q684).trans (apc661 q685 q685 q684 (q684 ◇ q685) q686)))
  have apc953:=fun (q687 q688:G)=>by
    exact ((((((cg (fun t => (((q688 ◇ q688) ◇ q687) ◇ q688) ◇ t) (cg (fun t => t ◇ (((q688 ◇ q687) ◇ q688) ◇ q688)) (apc6 q687 q688))).trans (cg (fun t => (((q688 ◇ q688) ◇ q687) ◇ q688) ◇ t) (apc326 q687 q688 q688 q688 ((q688 ◇ q687) ◇ q688)))).trans (cg (fun t => (((q688 ◇ q688) ◇ q687) ◇ q688) ◇ t) (apc21 q688 q687 q688 q688))).trans (cg (fun t => (((q688 ◇ q688) ◇ q687) ◇ q688) ◇ t) (apc760 q688 q688 q687))).trans (cg (fun t => (((q688 ◇ q688) ◇ q687) ◇ q688) ◇ t) (apc5 (q688 ◇ q687) q688 q687))).symm).trans ((((cg (fun t => t ◇ (((q688 ◇ (q688 ◇ q687)) ◇ (q688 ◇ q688)) ◇ (((q688 ◇ q687) ◇ q688) ◇ q688))) (apc6 q687 q688)).symm).trans (apc942 (q688 ◇ q687) q688)).trans (((((cg (fun t => t ◇ (((q688 ◇ q687) ◇ q688) ◇ q688)) (apc6 q687 q688)).trans (apc326 q687 q688 q688 q688 ((q688 ◇ q687) ◇ q688))).trans (apc21 q688 q687 q688 q688)).trans (apc760 q688 q688 q687)).trans (apc5 (q688 ◇ q687) q688 q687)))
  have apc954:=fun (q689 q690:G)=>by
    exact (((((((((((((cg (fun t => ((q690 ◇ (q690 ◇ (q690 ◇ q689))) ◇ q689) ◇ t) (cg (fun t => ((((q690 ◇ q690) ◇ q689) ◇ q690) ◇ ((q690 ◇ (q690 ◇ (q690 ◇ q689))) ◇ q689)) ◇ t) (apc396 q689 q690))).trans (cg (fun t => ((q690 ◇ (q690 ◇ (q690 ◇ q689))) ◇ q689) ◇ t) (cg (fun t => t ◇ (((q690 ◇ q689) ◇ (q690 ◇ q690)) ◇ q690)) (apc953 q689 q690)))).trans (cg (fun t => ((q690 ◇ (q690 ◇ (q690 ◇ q689))) ◇ q689) ◇ t) (apc4 ((q690 ◇ q689) ◇ (q690 ◇ q690)) q690 q689 (q690 ◇ (q690 ◇ q689))))).trans (cg (fun t => ((q690 ◇ (q690 ◇ (q690 ◇ q689))) ◇ q689) ◇ t) (apc321 q690 q690 q689 (q690 ◇ ((q690 ◇ q689) ◇ (q690 ◇ q690))) (((q690 ◇ (q690 ◇ q689)) ◇ (q690 ◇ q689)) ◇ (q690 ◇ ((q690 ◇ q689) ◇ (q690 ◇ q690)))) (((q690 ◇ (q690 ◇ q689)) ◇ (q690 ◇ q689)) ◇ (q690 ◇ ((q690 ◇ q689) ◇ (q690 ◇ q690)))) (((q690 ◇ (q690 ◇ q689)) ◇ (q690 ◇ q689)) ◇ (q690 ◇ ((q690 ◇ q689) ◇ (q690 ◇ q690)))) (((q690 ◇ (q690 ◇ q689)) ◇ (q690 ◇ q689)) ◇ (q690 ◇ ((q690 ◇ q689) ◇ (q690 ◇ q690)))) (((q690 ◇ (q690 ◇ q689)) ◇ (q690 ◇ q689)) ◇ (q690 ◇ ((q690 ◇ q689) ◇ (q690 ◇ q690))))))).trans (cg (fun t => ((q690 ◇ (q690 ◇ (q690 ◇ q689))) ◇ q689) ◇ t) (apc897 (q690 ◇ q689) q690 q690))).trans (apc661 q690 q690 ((q690 ◇ q689) ◇ q690) (q690 ◇ (q690 ◇ (q690 ◇ q689))) q689)).trans (cg (fun t => ((q690 ◇ (q690 ◇ (q690 ◇ q689))) ◇ q689) ◇ t) (apc292 q689 q690))).trans (apc630 q689 (q690 ◇ q689) q690 (q690 ◇ q689) q690)).trans (apc40 q689 q690 (q690 ◇ q689) q690)).trans (cg (fun t => t ◇ q690) (apc250 q689 q690 q689))).trans (apc582 q689 q690 q689 q690)).symm).trans ((((cg (fun t => t ◇ (((((q690 ◇ q690) ◇ q689) ◇ q690) ◇ ((q690 ◇ (q690 ◇ (q690 ◇ q689))) ◇ q689)) ◇ ((((q690 ◇ q690) ◇ q689) ◇ q690) ◇ q690))) (apc953 q689 q690)).symm).trans (apc946 ((q690 ◇ q690) ◇ q689) q690 ((q690 ◇ (q690 ◇ (q690 ◇ q689))) ◇ q689))).trans (((((cg (fun t => ((((q690 ◇ q690) ◇ q689) ◇ q690) ◇ ((q690 ◇ (q690 ◇ (q690 ◇ q689))) ◇ q689)) ◇ t) (apc396 q689 q690)).trans (cg (fun t => t ◇ (((q690 ◇ q689) ◇ (q690 ◇ q690)) ◇ q690)) (apc953 q689 q690))).trans (apc4 ((q690 ◇ q689) ◇ (q690 ◇ q690)) q690 q689 (q690 ◇ (q690 ◇ q689)))).trans (apc321 q690 q690 q689 (q690 ◇ ((q690 ◇ q689) ◇ (q690 ◇ q690))) (((q690 ◇ (q690 ◇ q689)) ◇ (q690 ◇ q689)) ◇ (q690 ◇ ((q690 ◇ q689) ◇ (q690 ◇ q690)))) (((q690 ◇ (q690 ◇ q689)) ◇ (q690 ◇ q689)) ◇ (q690 ◇ ((q690 ◇ q689) ◇ (q690 ◇ q690)))) (((q690 ◇ (q690 ◇ q689)) ◇ (q690 ◇ q689)) ◇ (q690 ◇ ((q690 ◇ q689) ◇ (q690 ◇ q690)))) (((q690 ◇ (q690 ◇ q689)) ◇ (q690 ◇ q689)) ◇ (q690 ◇ ((q690 ◇ q689) ◇ (q690 ◇ q690)))) (((q690 ◇ (q690 ◇ q689)) ◇ (q690 ◇ q689)) ◇ (q690 ◇ ((q690 ◇ q689) ◇ (q690 ◇ q690)))))).trans (apc897 (q690 ◇ q689) q690 q690)))).symm
  have apc1009:=fun (q691 q692:G)=>by
    exact (((apc954 q691 q692).symm).trans ((h ((q692 ◇ q691) ◇ q692) q692 q692).symm)).trans (apc292 q691 q692)
  have apc1010:=fun (q567 q568 q691 q692:G)=>by
    exact (apc611 q567 q568).trans (apc1009 q568 q567)
  have apc1011:=fun (q693 q694:G)=>by
    exact (((((apc695 q693 q694 (q694 ◇ q693)).trans (apc250 (q694 ◇ q693) q694 q693)).trans (apc239 q693 q694)).symm).trans ((((cg (fun t => (q694 ◇ (q694 ◇ q693)) ◇ t) (apc6 q693 q694)).symm).trans (apc941 q693 q693 q693 (q694 ◇ q693) q694)).trans (apc6 q693 q694))).symm
  have apc1015:=fun (q695 q696 q697:G)=>by
    exact (((apc662 q696 q695 q696 q696 q697 ((q697 ◇ q696) ◇ (((q696 ◇ q695) ◇ q696) ◇ q696)) ((q697 ◇ q696) ◇ (((q696 ◇ q695) ◇ q696) ◇ q696)) ((q697 ◇ q696) ◇ (((q696 ◇ q695) ◇ q696) ◇ q696)) ((q697 ◇ q696) ◇ (((q696 ◇ q695) ◇ q696) ◇ q696)) ((q697 ◇ q696) ◇ (((q696 ◇ q695) ◇ q696) ◇ q696))).symm).trans (((cg (fun t => (q697 ◇ q696) ◇ t) (apc1011 q695 q696)).symm).trans ((h q696 q697 ((q696 ◇ q696) ◇ q695)).symm))).symm
  have apc1016:=fun (q698 q699:G)=>by
    exact ((apc1015 q698 q699 q698).symm).trans ((h q698 q699 (q699 ◇ q699)).symm)
  have apc1018:=fun (q611 q612 q613 q693 q694:G)=>by
    exact (((apc688 q611 q612 q613).symm).trans (((cg (fun t => (q612 ◇ q613) ◇ t) (apc1011 q611 q612)).symm).trans (apc695 q611 q612 q613))).symm
  have apc1019:=fun (q679 q680 q681 q404 q405 q611 q612 q613 q693 q694:G)=>by
    exact ((apc1018 q404 q405 q404 ((q405 ◇ q404) ◇ ((q405 ◇ q404) ◇ (q405 ◇ q405))) ((q405 ◇ q404) ◇ ((q405 ◇ q404) ◇ (q405 ◇ q405)))).symm).trans (apc941 q404 q404 q404 q404 q405)
  have apc1020:=fun (q679 q680 q681 q611 q612 q613 q693 q694:G)=>by
    exact (apc940 q679 q680 q681).trans (apc1018 q679 q680 q681 ((q680 ◇ q681) ◇ ((q680 ◇ q679) ◇ (q680 ◇ q680))) ((q680 ◇ q681) ◇ ((q680 ◇ q679) ◇ (q680 ◇ q680))))
  have apc1028:=fun (q700 q701:G)=>by
    exact (((apc70 q701 q700 ((q701 ◇ (q701 ◇ q700)) ◇ (q701 ◇ (q701 ◇ q700))) ((q701 ◇ (q701 ◇ q700)) ◇ (q701 ◇ (q701 ◇ q700))) ((q701 ◇ (q701 ◇ q700)) ◇ (q701 ◇ (q701 ◇ q700))) ((q701 ◇ (q701 ◇ q700)) ◇ (q701 ◇ (q701 ◇ q700))) ((q701 ◇ (q701 ◇ q700)) ◇ (q701 ◇ (q701 ◇ q700)))).symm).trans (((apc1020 q700 q701 (q701 ◇ q700) q700 q700 q700 q700 q700).symm).trans ((h (q701 ◇ q700) q701 (q701 ◇ q701)).symm))).symm
  have apc1029:=fun (q700 q701 q567 q568 q691 q692:G)=>by
    exact (apc1010 q567 q568 q567 q567).trans (apc1028 q568 q567)
  have apc1030:=fun (q702 q703:G)=>by
    exact ((apc1028 q702 q703).symm).trans ((h q703 (q703 ◇ q702) q703).symm)
  have apc1031:=fun (q704 q705 q706:G)=>by
    exact (((apc67 q704 q705 q706 ((q706 ◇ q705) ◇ ((q705 ◇ (q705 ◇ q704)) ◇ q705)) ((q706 ◇ q705) ◇ ((q705 ◇ (q705 ◇ q704)) ◇ q705)) ((q706 ◇ q705) ◇ ((q705 ◇ (q705 ◇ q704)) ◇ q705))).symm).trans (((cg (fun t => (q706 ◇ q705) ◇ t) (apc1030 q704 q705)).symm).trans ((h q705 q706 ((q705 ◇ q704) ◇ q705)).symm))).symm
  have apc1032:=fun (q707 q708:G)=>by
    exact ((apc1019 ((q708 ◇ q707) ◇ (q708 ◇ (q708 ◇ q707))) ((q708 ◇ q707) ◇ (q708 ◇ (q708 ◇ q707))) ((q708 ◇ q707) ◇ (q708 ◇ (q708 ◇ q707))) q707 q708 ((q708 ◇ q707) ◇ (q708 ◇ (q708 ◇ q707))) ((q708 ◇ q707) ◇ (q708 ◇ (q708 ◇ q707))) ((q708 ◇ q707) ◇ (q708 ◇ (q708 ◇ q707))) ((q708 ◇ q707) ◇ (q708 ◇ (q708 ◇ q707))) ((q708 ◇ q707) ◇ (q708 ◇ (q708 ◇ q707)))).symm).trans (((apc1031 q707 q708 q707).symm).trans (apc1016 q707 q708))
  have apc1033:=fun (q709:G)=>by
    exact ((apc1032 q709 q709).symm).trans ((h q709 q709 q709).symm)
  have apc1036:=fun (q704 q705 q710:G)=>by
    exact ((((((apc4 q710 q705 q705 (q705 ◇ q704)).trans (cg (fun t => t ◇ (q705 ◇ q710)) (apc1032 q704 q705))).trans (apc5 (q704 ◇ q705) q705 q710)).trans (apc10 q704 q705 q710)).symm).trans (((cg (fun t => t ◇ (q710 ◇ q705)) (apc1030 q704 q705)).symm).trans ((h q705 ((q705 ◇ q704) ◇ q705) q710).symm))).symm
  have apc1037:=fun (q704 q705 q710 q415 q416:G)=>by
    exact (apc375 q415 q416).trans (apc1036 q416 q415 q416)
  have apc1038:=fun (q700 q701 q691 q692:G)=>by
    exact (apc1009 q691 q692).trans (apc1028 q691 q692)
  have apc1043:=fun (q711 q712 q713:G)=>by
    exact ((((apc5 (q711 ◇ q712) q712 q713).trans (apc10 q711 q712 q713)).symm).trans (((cg (fun t => t ◇ (q712 ◇ q713)) (apc1032 q711 q712)).symm).trans (apc5 (q712 ◇ q711) q712 q713))).symm
  have apc1044:=fun (q311 q312 q313 q711 q712 q713 q100 q101 q102:G)=>by
    exact (apc502 q100 q100 q100 q100 q101 q102).trans (apc1043 q100 q102 q101)
  have apc1045:=fun (q311 q312 q313 q711 q712 q713 q437 q438 q100 q101 q102:G)=>by
    exact ((apc430 q437 q438).trans (apc1044 ((q437 ◇ ((q437 ◇ q437) ◇ q438)) ◇ q437) ((q437 ◇ ((q437 ◇ q437) ◇ q438)) ◇ q437) ((q437 ◇ ((q437 ◇ q437) ◇ q438)) ◇ q437) ((q437 ◇ ((q437 ◇ q437) ◇ q438)) ◇ q437) ((q437 ◇ ((q437 ◇ q437) ◇ q438)) ◇ q437) ((q437 ◇ ((q437 ◇ q437) ◇ q438)) ◇ q437) q438 q437 q437)).trans (apc1028 q438 q437)
  have apc1048:=fun (q311 q312 q313 q711 q712 q713 q362 q363 q100 q101 q102:G)=>by
    exact ((apc284 q362 q363).trans (apc1044 ((q362 ◇ ((q362 ◇ q362) ◇ q363)) ◇ q362) ((q362 ◇ ((q362 ◇ q362) ◇ q363)) ◇ q362) ((q362 ◇ ((q362 ◇ q362) ◇ q363)) ◇ q362) ((q362 ◇ ((q362 ◇ q362) ◇ q363)) ◇ q362) ((q362 ◇ ((q362 ◇ q362) ◇ q363)) ◇ q362) ((q362 ◇ ((q362 ◇ q362) ◇ q363)) ◇ q362) q363 q362 q362)).trans (apc1028 q363 q362)
  have apc1050:=fun (q714 q715 q716:G)=>by
    exact (((apc662 q715 q714 q715 q715 q716 ((q716 ◇ q715) ◇ (((q715 ◇ q714) ◇ q715) ◇ q715)) ((q716 ◇ q715) ◇ (((q715 ◇ q714) ◇ q715) ◇ q715)) ((q716 ◇ q715) ◇ (((q715 ◇ q714) ◇ q715) ◇ q715)) ((q716 ◇ q715) ◇ (((q715 ◇ q714) ◇ q715) ◇ q715)) ((q716 ◇ q715) ◇ (((q715 ◇ q714) ◇ q715) ◇ q715))).symm).trans (((cg (fun t => (q716 ◇ q715) ◇ t) (apc1038 q714 q714 q714 q715)).symm).trans ((h q715 q716 (((q715 ◇ q715) ◇ q714) ◇ q714)).symm))).symm
  have apc1051:=fun (q717 q718:G)=>by
    exact (((apc1016 q717 q718).symm).trans (((apc1050 q717 q718 q717).symm).trans ((h q717 q718 ((q718 ◇ q718) ◇ q717)).symm))).symm
  have apc1053:=fun (q719 q720:G)=>by
    exact ((cg (fun t => t ◇ q719) (apc1032 q720 q719)).symm).trans (apc1045 q719 q719 q719 q719 q719 q719 q719 q720 q719 q719 q719)
  have apc1056:=fun (q721 q722:G)=>by
    exact ((((((cg (fun t => t ◇ (q722 ◇ q722)) (apc1032 q721 q722)).trans (apc5 (q721 ◇ q722) q722 q722)).trans (apc10 q721 q722 q722)).trans (apc1028 q721 q722)).symm).trans (((cg (fun t => t ◇ (q722 ◇ q722)) (apc225 q721 q721 q722 q721)).symm).trans (apc1048 q721 q721 q721 q721 q721 q721 q722 (q722 ◇ q721) q721 q721 q721))).symm
  have apc1057:=fun (q723 q724 q725:G)=>by
    exact (((apc662 q724 q723 q724 q724 q725 ((q725 ◇ q724) ◇ (((q724 ◇ q723) ◇ q724) ◇ q724)) ((q725 ◇ q724) ◇ (((q724 ◇ q723) ◇ q724) ◇ q724)) ((q725 ◇ q724) ◇ (((q724 ◇ q723) ◇ q724) ◇ q724)) ((q725 ◇ q724) ◇ (((q724 ◇ q723) ◇ q724) ◇ q724)) ((q725 ◇ q724) ◇ (((q724 ◇ q723) ◇ q724) ◇ q724))).symm).trans (((cg (fun t => (q725 ◇ q724) ◇ t) (apc1056 q723 q724)).symm).trans ((h q724 q725 ((q724 ◇ (q724 ◇ q723)) ◇ q724)).symm))).symm
  have apc1058:=fun (q726 q727:G)=>by
    exact (((apc1057 q726 q727 (q727 ◇ q726)).symm).trans (apc1016 (q727 ◇ q726) q727)).trans (apc1028 q726 q727)
  have apc1069:=fun (q695 q696 q697 q617 q618 q619:G)=>by
    exact (((apc1044 ((q619 ◇ ((q619 ◇ q619) ◇ q618)) ◇ ((q619 ◇ q617) ◇ q619)) ((q619 ◇ ((q619 ◇ q619) ◇ q618)) ◇ ((q619 ◇ q617) ◇ q619)) ((q619 ◇ ((q619 ◇ q619) ◇ q618)) ◇ ((q619 ◇ q617) ◇ q619)) ((q619 ◇ ((q619 ◇ q619) ◇ q618)) ◇ ((q619 ◇ q617) ◇ q619)) ((q619 ◇ ((q619 ◇ q619) ◇ q618)) ◇ ((q619 ◇ q617) ◇ q619)) ((q619 ◇ ((q619 ◇ q619) ◇ q618)) ◇ ((q619 ◇ q617) ◇ q619)) q618 ((q619 ◇ q617) ◇ q619) q619).trans (apc503 q618 q617 q619)).symm).trans (((apc1015 q617 q619 ((q619 ◇ q619) ◇ q618)).symm).trans (apc703 q617 q618 q619))
  have apc1071:=fun (q339 q340 q341 q695 q696 q697 q617 q618 q619:G)=>by
    exact (((apc1069 (((q340 ◇ q340) ◇ q341) ◇ ((q339 ◇ q340) ◇ q340)) (((q340 ◇ q340) ◇ q341) ◇ ((q339 ◇ q340) ◇ q340)) (((q340 ◇ q340) ◇ q341) ◇ ((q339 ◇ q340) ◇ q340)) q339 q341 q340).symm).trans (apc251 q339 q340 q341)).symm
  have apc1073:=fun (q339 q340 q341 q695 q696 q697 q726 q727 q617 q618 q619:G)=>by
    exact ((apc1071 q726 q727 q726 ((q727 ◇ (q727 ◇ q726)) ◇ ((q727 ◇ q726) ◇ q727)) ((q727 ◇ (q727 ◇ q726)) ◇ ((q727 ◇ q726) ◇ q727)) ((q727 ◇ (q727 ◇ q726)) ◇ ((q727 ◇ q726) ◇ q727)) ((q727 ◇ (q727 ◇ q726)) ◇ ((q727 ◇ q726) ◇ q727)) ((q727 ◇ (q727 ◇ q726)) ◇ ((q727 ◇ q726) ◇ q727)) ((q727 ◇ (q727 ◇ q726)) ◇ ((q727 ◇ q726) ◇ q727))).symm).trans (apc1058 q726 q727)
  have apc1078:=fun (q728 q729 q730:G)=>by
    exact ((cg (fun t => (q730 ◇ q729) ◇ t) (apc1073 q728 q728 q728 q728 q728 q728 q729 q728 q728 q728 q728)).symm).trans ((h q729 q730 ((q728 ◇ (q728 ◇ q728)) ◇ q729)).symm)
  have apc1082:=fun (q711 q712 q713 q614 q615 q616 q569 q570 q571:G)=>by
    exact (((apc17 q569 q570 q571).symm).trans (((apc1043 q569 q571 (q571 ◇ q570)).symm).trans (apc701 q569 q569 q569 q569 q570 q571))).symm
  have apc1085:=fun (q731 q732 q733 q734:G)=>by
    exact (((cg (fun t => (q733 ◇ q734) ◇ t) (apc1032 (q731 ◇ q732) q731)).trans (cg (fun t => (q733 ◇ q734) ◇ t) (apc1028 q732 q731))).symm).trans (((cg (fun t => (q733 ◇ q734) ◇ t) (apc5 q732 q731 (q731 ◇ q731))).symm).trans (apc661 q731 q732 (q731 ◇ q731) q733 q734))
  have apc1088:=fun (q728 q729 q730 q731 q732 q733 q734:G)=>by
    exact ((apc1085 q728 q729 q730 q729).symm).trans (apc1078 q728 q729 q730)
  have apc1100:=fun (q735 q736 q737:G)=>by
    exact ((apc661 q736 (q736 ◇ q735) q735 q737 q736).symm).trans (((cg (fun t => (q737 ◇ q736) ◇ t) (apc804 q735 q735 q735 q735 q736 q735 q735)).symm).trans ((h q736 q737 (q735 ◇ ((q736 ◇ q735) ◇ q736))).symm))
  have apc1102:=fun (q738 q739 q740:G)=>by
    exact ((apc1100 q738 q739 q740).symm).trans ((h q739 q740 (q738 ◇ (q739 ◇ q738))).symm)
  have apc1104:=fun (q741 q742:G)=>by
    exact (((apc1036 q742 q741 (q742 ◇ (q741 ◇ q742))).trans (apc521 (q741 ◇ q742) q741 q741 q742)).symm).trans ((((apc1102 q742 q741 ((q741 ◇ q742) ◇ q741)).symm).trans ((h ((q741 ◇ q742) ◇ q741) q741 q742).symm)).trans (apc1037 ((((q741 ◇ q742) ◇ q741) ◇ q741) ◇ q742) ((((q741 ◇ q742) ◇ q741) ◇ q741) ◇ q742) ((((q741 ◇ q742) ◇ q741) ◇ q741) ◇ q742) q741 q742))
  have apc1105:=fun (q743 q744:G)=>by
    exact ((apc1104 q744 q743).symm).trans ((h (q744 ◇ q743) q744 (q743 ◇ q744)).symm)
  have apc1107:=fun (q745 q746 q747:G)=>by
    exact ((((apc661 q746 q745 q746 q747 (q746 ◇ q746)).trans (apc1 q746 q745 q746 q747)).symm).trans (((cg (fun t => (q747 ◇ (q746 ◇ q746)) ◇ t) (apc1032 q745 q746)).symm).trans ((h (q746 ◇ q746) q747 (q746 ◇ q745)).symm))).symm
  have apc1108:=fun (q748 q749:G)=>by
    exact ((apc1107 q748 q749 q748).symm).trans ((h q748 (q749 ◇ q749) q749).symm)
  have apc1109:=fun (q750 q751:G)=>by
    exact ((((apc1082 (((q750 ◇ q750) ◇ (q750 ◇ (q751 ◇ q751))) ◇ (q751 ◇ q751)) (((q750 ◇ q750) ◇ (q750 ◇ (q751 ◇ q751))) ◇ (q751 ◇ q751)) (((q750 ◇ q750) ◇ (q750 ◇ (q751 ◇ q751))) ◇ (q751 ◇ q751)) (((q750 ◇ q750) ◇ (q750 ◇ (q751 ◇ q751))) ◇ (q751 ◇ q751)) (((q750 ◇ q750) ◇ (q750 ◇ (q751 ◇ q751))) ◇ (q751 ◇ q751)) (((q750 ◇ q750) ◇ (q750 ◇ (q751 ◇ q751))) ◇ (q751 ◇ q751)) (q751 ◇ q751) (q751 ◇ q751) q750).trans (apc1108 (q751 ◇ q751) q750)).symm).trans (((cg (fun t => t ◇ (q751 ◇ q751)) (apc689 (q751 ◇ q751) q750)).symm).trans (apc1029 q750 q750 q751 (q750 ◇ q750) q750 q750))).symm
  have apc1113:=fun (q745 q746 q747 q417 q418 q419:G)=>by
    exact (((apc699 q419 q418 q417).symm).trans (((apc1107 q417 q418 (q418 ◇ q419)).symm).trans (apc390 q417 q418 q419))).symm
  have apc1118:=fun (q745 q746 q747 q417 q418 q419 q159 q160 q161:G)=>by
    exact ((apc1113 (((q159 ◇ (q159 ◇ q159)) ◇ q160) ◇ (q161 ◇ q160)) (((q159 ◇ (q159 ◇ q159)) ◇ q160) ◇ (q161 ◇ q160)) (((q159 ◇ (q159 ◇ q159)) ◇ q160) ◇ (q161 ◇ q160)) (q161 ◇ q160) q159 q160).symm).trans (apc98 q159 q160 q161)
  have apc1121:=fun (q339 q340 q341 q695 q696 q697 q745 q746 q747 q726 q727 q417 q418 q419 q617 q618 q619:G)=>by
    exact ((apc1113 (((q727 ◇ (q727 ◇ q727)) ◇ q726) ◇ q726) (((q727 ◇ (q727 ◇ q727)) ◇ q726) ◇ q726) (((q727 ◇ (q727 ◇ q727)) ◇ q726) ◇ q726) q726 q727 q726).symm).trans (apc1073 q726 q726 q726 q726 q726 q726 q726 q727 q726 q726 q726)
  have apc1124:=fun (q339 q340 q341 q695 q696 q697 q745 q746 q747 q417 q418 q419 q617 q618 q619:G)=>by
    exact (apc1071 q339 q340 q341 q339 q339 q339 q339 q339 q339).trans (apc1113 (((q340 ◇ (q340 ◇ q340)) ◇ q341) ◇ q339) (((q340 ◇ (q340 ◇ q340)) ◇ q341) ◇ q339) (((q340 ◇ (q340 ◇ q340)) ◇ q341) ◇ q339) q339 q340 q341)
  have apc1126:=fun (q752 q753 q754:G)=>by
    exact (((apc1085 q752 q753 q754 q753).trans (apc1088 q752 q753 q754 ((q754 ◇ q753) ◇ (((q752 ◇ q752) ◇ q753) ◇ q752)) ((q754 ◇ q753) ◇ (((q752 ◇ q752) ◇ q753) ◇ q752)) ((q754 ◇ q753) ◇ (((q752 ◇ q752) ◇ q753) ◇ q752)) ((q754 ◇ q753) ◇ (((q752 ◇ q752) ◇ q753) ◇ q752)))).symm).trans (((cg (fun t => (q754 ◇ q753) ◇ t) (apc1121 q752 q752 q752 q752 q752 q752 q752 q752 q752 q753 q752 q752 q752 q752 q752 q752 q752)).symm).trans ((h q753 q754 ((q752 ◇ q752) ◇ (q752 ◇ q753))).symm))
  have apc1128:=fun (q728 q729 q730 q752 q753 q754 q731 q732 q733 q734:G)=>by
    exact (apc1088 q728 q729 q730 q728 q728 q728 q728).trans (apc1126 q728 q729 q730)
  have apc1133:=fun (q755 q756 q757:G)=>by
    exact (((apc870 q755 q756 q757).symm).trans (((cg (fun t => (q757 ◇ q756) ◇ t) (apc1109 q755 q756)).symm).trans ((h q756 q757 ((q756 ◇ (q755 ◇ q755)) ◇ q756)).symm))).symm
  have apc1135:=fun (q758 q759:G)=>by
    exact ((((apc5 q759 q758 (q758 ◇ (q759 ◇ q759))).trans (apc95 q759 q759 q758)).symm).trans (((apc1133 q758 q759 (q758 ◇ q758)).symm).trans (apc1016 (q758 ◇ q758) q759))).symm
  have apc1136:=fun (q760 q761:G)=>by
    exact ((apc1135 q760 q761).symm).trans ((h q761 (q760 ◇ q760) q761).symm)
  have apc1142:=fun (q762 q763:G)=>by
    exact (((((apc5 (q762 ◇ q763) q763 q763).trans (apc10 q762 q763 q763)).trans (apc1028 q762 q763)).symm).trans ((((cg (fun t => t ◇ (q763 ◇ q763)) (apc1016 q762 q763)).symm).trans (apc1136 (q763 ◇ q762) q763)).trans (apc327 ((q763 ◇ ((q763 ◇ q762) ◇ (q763 ◇ q762))) ◇ q763) ((q763 ◇ ((q763 ◇ q762) ◇ (q763 ◇ q762))) ◇ q763) ((q763 ◇ ((q763 ◇ q762) ◇ (q763 ◇ q762))) ◇ q763) ((q763 ◇ ((q763 ◇ q762) ◇ (q763 ◇ q762))) ◇ q763) ((q763 ◇ ((q763 ◇ q762) ◇ (q763 ◇ q762))) ◇ q763) q763 q763 q762 q763 q763))).symm
  have apc1143:=fun (q764 q765 q766:G)=>by
    exact (((apc662 q765 q764 q765 q765 q766 ((q766 ◇ q765) ◇ (((q765 ◇ q764) ◇ q765) ◇ q765)) ((q766 ◇ q765) ◇ (((q765 ◇ q764) ◇ q765) ◇ q765)) ((q766 ◇ q765) ◇ (((q765 ◇ q764) ◇ q765) ◇ q765)) ((q766 ◇ q765) ◇ (((q765 ◇ q764) ◇ q765) ◇ q765)) ((q766 ◇ q765) ◇ (((q765 ◇ q764) ◇ q765) ◇ q765))).symm).trans (((cg (fun t => (q766 ◇ q765) ◇ t) (apc1142 q764 q765)).symm).trans ((h q765 q766 (q765 ◇ ((q764 ◇ q765) ◇ q765))).symm))).symm
  have apc1144:=fun (q767 q768:G)=>by
    exact (((((apc42 q767 q768 q768 q768).trans (cg (fun t => t ◇ q768) (apc1016 q767 q768))).trans (apc1053 q768 q767)).symm).trans (((apc1143 q767 q768 ((q767 ◇ q768) ◇ q768)).symm).trans ((h ((q767 ◇ q768) ◇ q768) q768 q768).symm))).symm
  have apc1146:=fun (q769 q770 q771:G)=>by
    exact (((apc662 q770 q769 q770 q770 q771 ((q771 ◇ q770) ◇ (((q770 ◇ q769) ◇ q770) ◇ q770)) ((q771 ◇ q770) ◇ (((q770 ◇ q769) ◇ q770) ◇ q770)) ((q771 ◇ q770) ◇ (((q770 ◇ q769) ◇ q770) ◇ q770)) ((q771 ◇ q770) ◇ (((q770 ◇ q769) ◇ q770) ◇ q770)) ((q771 ◇ q770) ◇ (((q770 ◇ q769) ◇ q770) ◇ q770))).symm).trans (((cg (fun t => (q771 ◇ q770) ◇ t) (apc1144 q769 q770)).symm).trans ((h q770 q771 (((q769 ◇ q770) ◇ q770) ◇ q770)).symm))).symm
  have apc1147:=fun (q772 q773:G)=>by
    exact (((apc491 q772 q773 ((q773 ◇ q773) ◇ ((q773 ◇ q772) ◇ q773)) ((q773 ◇ q773) ◇ ((q773 ◇ q772) ◇ q773))).symm).trans (((apc1146 q772 q773 q773).symm).trans ((h q773 q773 ((q772 ◇ q773) ◇ q773)).symm))).symm
  have apc1148:=fun (q774 q775:G)=>by
    exact ((apc1147 q774 q775).symm).trans ((h q775 q775 (q774 ◇ q775)).symm)
  have apc1153:=fun (q711 q712 q713 q774 q775 q614 q615 q616 q569 q570 q571:G)=>by
    exact ((cg (fun t => t ◇ q570) (apc1148 q569 q571)).symm).trans (apc1082 q569 q569 q569 q569 q569 q569 q569 q570 q571)
  have apc1154:=fun (q776 q777 q778:G)=>by
    exact (((cg (fun t => t ◇ q777) ((h q778 q778 q776).symm)).symm).trans (apc1153 q776 q776 q776 q776 q776 q776 q776 q776 q776 q777 q778)).symm
  have apc1156:=fun (q776 q777 q778 q745 q746 q747:G)=>by
    exact (apc1107 q745 q746 q747).trans (apc1154 q747 q745 q746)
  have apc1157:=fun (q776 q777 q778 q748 q749:G)=>by
    exact (((apc1154 q748 q748 q749).symm).trans (apc1108 q748 q749)).symm
  have apc1158:=fun (q776 q777 q778 q332 q333:G)=>by
    exact ((apc1156 (((q333 ◇ q333) ◇ q332) ◇ (q333 ◇ q332)) (((q333 ◇ q333) ◇ q332) ◇ (q333 ◇ q332)) (((q333 ◇ q333) ◇ q332) ◇ (q333 ◇ q332)) q332 q333 q332).symm).trans (((apc1154 q332 (q333 ◇ q332) q333).symm).trans (apc239 q332 q333))
  have apc1159:=fun (q776 q777 q778 q748 q749 q332 q333:G)=>by
    exact ((apc1157 q748 q748 q748 q748 q749).trans (apc1158 (((q749 ◇ q749) ◇ q748) ◇ q748) (((q749 ◇ q749) ◇ q748) ◇ q748) (((q749 ◇ q749) ◇ q748) ◇ q748) q748 q749)).symm
  have apc1162:=fun (q776 q777 q778 q336 q337 q338:G)=>by
    exact (apc250 q336 q337 q338).trans (apc1154 q338 q336 q337)
  have apc1165:=fun (q779 q780 q781:G)=>by
    exact (((apc1085 q779 q780 q781 q780).trans (apc1128 q779 q780 q781 ((q781 ◇ q780) ◇ (((q779 ◇ q779) ◇ q780) ◇ q779)) ((q781 ◇ q780) ◇ (((q779 ◇ q779) ◇ q780) ◇ q779)) ((q781 ◇ q780) ◇ (((q779 ◇ q779) ◇ q780) ◇ q779)) ((q781 ◇ q780) ◇ (((q779 ◇ q779) ◇ q780) ◇ q779)) ((q781 ◇ q780) ◇ (((q779 ◇ q779) ◇ q780) ◇ q779)) ((q781 ◇ q780) ◇ (((q779 ◇ q779) ◇ q780) ◇ q779)) ((q781 ◇ q780) ◇ (((q779 ◇ q779) ◇ q780) ◇ q779)))).symm).trans (((cg (fun t => (q781 ◇ q780) ◇ t) (apc1158 q779 q779 q779 q780 q779)).symm).trans ((h q780 q781 ((q779 ◇ q779) ◇ q780)).symm))
  have apc1172:=fun (q728 q729 q730 q752 q753 q754 q779 q780 q781 q731 q732 q733 q734:G)=>by
    exact (apc1128 q728 q729 q730 q728 q728 q728 q728 q728 q728 q728).trans (apc1165 q728 q729 q730)
  have apc1203:=fun (q782 q783 q784:G)=>by
    exact ((apc1124 q782 q783 q784 ((q783 ◇ (q783 ◇ q784)) ◇ ((q783 ◇ q782) ◇ q783)) ((q783 ◇ (q783 ◇ q784)) ◇ ((q783 ◇ q782) ◇ q783)) ((q783 ◇ (q783 ◇ q784)) ◇ ((q783 ◇ q782) ◇ q783)) ((q783 ◇ (q783 ◇ q784)) ◇ ((q783 ◇ q782) ◇ q783)) ((q783 ◇ (q783 ◇ q784)) ◇ ((q783 ◇ q782) ◇ q783)) ((q783 ◇ (q783 ◇ q784)) ◇ ((q783 ◇ q782) ◇ q783)) ((q783 ◇ (q783 ◇ q784)) ◇ ((q783 ◇ q782) ◇ q783)) ((q783 ◇ (q783 ◇ q784)) ◇ ((q783 ◇ q782) ◇ q783)) ((q783 ◇ (q783 ◇ q784)) ◇ ((q783 ◇ q782) ◇ q783)) ((q783 ◇ (q783 ◇ q784)) ◇ ((q783 ◇ q782) ◇ q783)) ((q783 ◇ (q783 ◇ q784)) ◇ ((q783 ◇ q782) ◇ q783)) ((q783 ◇ (q783 ◇ q784)) ◇ ((q783 ◇ q782) ◇ q783))).symm).trans ((((cg (fun t => (q783 ◇ (q783 ◇ q784)) ◇ t) ((h q783 q782 q783).symm)).symm).trans (apc1162 q782 q782 q782 (q782 ◇ q783) q783 q784)).trans (apc1154 q784 q782 q783))
  have apc1205:=fun (q782 q783 q784 q745 q746 q747 q417 q418 q419 q159 q160 q161:G)=>by
    exact (((apc1203 (q161 ◇ q160) q159 q160).symm).trans (apc1118 q159 q159 q159 q159 q159 q159 q159 q160 q161)).symm
  have apc1221:=fun (q785 q786:G)=>by
    exact (((((apc1205 ((q786 ◇ ((q785 ◇ q785) ◇ q785)) ◇ (q785 ◇ q785)) ((q786 ◇ ((q785 ◇ q785) ◇ q785)) ◇ (q785 ◇ q785)) ((q786 ◇ ((q785 ◇ q785) ◇ q785)) ◇ (q785 ◇ q785)) ((q786 ◇ ((q785 ◇ q785) ◇ q785)) ◇ (q785 ◇ q785)) ((q786 ◇ ((q785 ◇ q785) ◇ q785)) ◇ (q785 ◇ q785)) ((q786 ◇ ((q785 ◇ q785) ◇ q785)) ◇ (q785 ◇ q785)) ((q786 ◇ ((q785 ◇ q785) ◇ q785)) ◇ (q785 ◇ q785)) ((q786 ◇ ((q785 ◇ q785) ◇ q785)) ◇ (q785 ◇ q785)) ((q786 ◇ ((q785 ◇ q785) ◇ q785)) ◇ (q785 ◇ q785)) q785 q786 (q785 ◇ q785)).trans (apc3 q785 q785 q785 q786)).trans (apc1028 q786 q785)).symm).trans ((((cg (fun t => t ◇ (q785 ◇ q785)) (cg (fun t => q786 ◇ t) (apc1033 q785))).symm).trans (apc1157 q785 q785 q785 q786 (q785 ◇ q785))).trans (cg (fun t => t ◇ q786) (cg (fun t => t ◇ q786) (apc1033 q785))))).symm
  have apc1222:=fun (q787 q788:G)=>by
    exact ((((((apc929 q788 q788 q787).trans (cg (fun t => t ◇ (q788 ◇ q787)) (apc1032 q787 q788))).trans (apc5 (q787 ◇ q788) q788 q787)).trans (apc10 q787 q788 q787)).trans (apc1105 q787 q788)).symm).trans ((((cg (fun t => t ◇ (q787 ◇ q788)) (apc1154 q788 q787 q788)).symm).trans (apc1221 q788 (q787 ◇ q788))).trans ((apc1159 (((q788 ◇ (q787 ◇ q788)) ◇ q788) ◇ q788) (((q788 ◇ (q787 ◇ q788)) ◇ q788) ◇ q788) (((q788 ◇ (q787 ◇ q788)) ◇ q788) ◇ q788) (q787 ◇ q788) q788 (((q788 ◇ (q787 ◇ q788)) ◇ q788) ◇ q788) (((q788 ◇ (q787 ◇ q788)) ◇ q788) ◇ q788)).trans (apc1053 q788 q787)))
  have apc1224:=fun (q789 q790:G)=>by
    exact (((apc1222 q790 q789).symm).trans ((h q789 (q789 ◇ q790) q790).symm)).symm
  have apc1226:=fun (q791 q792 q793:G)=>by
    exact (((apc1085 q791 q792 q793 q792).trans (apc1172 q791 q792 q793 ((q793 ◇ q792) ◇ (((q791 ◇ q791) ◇ q792) ◇ q791)) ((q793 ◇ q792) ◇ (((q791 ◇ q791) ◇ q792) ◇ q791)) ((q793 ◇ q792) ◇ (((q791 ◇ q791) ◇ q792) ◇ q791)) ((q793 ◇ q792) ◇ (((q791 ◇ q791) ◇ q792) ◇ q791)) ((q793 ◇ q792) ◇ (((q791 ◇ q791) ◇ q792) ◇ q791)) ((q793 ◇ q792) ◇ (((q791 ◇ q791) ◇ q792) ◇ q791)) ((q793 ◇ q792) ◇ (((q791 ◇ q791) ◇ q792) ◇ q791)) ((q793 ◇ q792) ◇ (((q791 ◇ q791) ◇ q792) ◇ q791)) ((q793 ◇ q792) ◇ (((q791 ◇ q791) ◇ q792) ◇ q791)) ((q793 ◇ q792) ◇ (((q791 ◇ q791) ◇ q792) ◇ q791)))).symm).trans (((cg (fun t => (q793 ◇ q792) ◇ t) (apc1224 q791 q792)).symm).trans ((h q792 q793 (q791 ◇ (q791 ◇ q792))).symm))
  have apc1227:=fun (q794 q795:G)=>by
    exact ((apc1226 q795 q794 q795).symm).trans (apc1051 q794 q795)
  have apc1278:=fun (q796 q797 q798:G)=>by
    exact (((apc84 q796 q798 q797).symm).trans (((apc1203 (q798 ◇ (q796 ◇ q797)) q796 q797).symm).trans ((h (q796 ◇ q797) (q796 ◇ q796) q798).symm))).symm
  have apc1282:=fun (q799 q800 q801:G)=>by
    exact ((cg (fun t => t ◇ q801) (apc1032 q800 q799)).symm).trans (apc1278 q799 q800 q801)
  have apc1283:=fun (q802 q803 q804:G)=>by
    exact ((cg (fun t => t ◇ q804) ((h q802 q803 q802).symm)).symm).trans (apc1282 q802 q803 q804)
  have apc1286:=fun (q805 q806 q807 q808:G)=>by
    exact ((cg (fun t => (q808 ◇ q807) ◇ t) (apc1283 q805 q806 q807)).symm).trans ((h q807 q808 ((q805 ◇ q806) ◇ q805)).symm)
  have apc1288:=fun (q809 q810 q811 q812:G)=>by
    exact ((apc1286 q809 q810 q811 q812).symm).trans ((h q811 q812 (q809 ◇ (q809 ◇ q810))).symm)
  have apc1289:=fun (q813 q814 q815:G)=>by
    exact ((apc1288 q814 q813 q815 q814).symm).trans ((h q814 q815 (q814 ◇ q813)).symm)
  have apc1290:=fun (q794 q795 q813 q814 q815:G)=>by
    exact ((apc1289 q794 q795 q794).symm).trans (apc1227 q794 q795)
  have apc1291:=fun (q816 q817:G)=>by
    exact ((apc1290 q816 q817 q816 q816 q816).symm).trans ((h q816 q817 q817).symm)
  have apc1293:=fun (q794 q795 q813 q814 q815 q816 q817:G)=>by
    exact (apc1290 q794 q795 q794 q794 q794).trans (apc1291 q794 q795)
  have apc1294:=fun (q818 q819:G)=>by
    exact (((apc1291 q818 q819).symm).trans ((h q819 q818 q819).symm)).symm
  have apc1300:=fun (q820 q821 q822:G)=>by
    exact ((cg (fun t => (q822 ◇ q821) ◇ t) (apc1294 q820 q821)).symm).trans ((h q821 q822 (q821 ◇ q820)).symm)
  have apc1302:=fun (q823 q824 q825:G)=>by
    exact ((apc1300 q823 q824 q825).symm).trans ((h q824 q825 (q823 ◇ q824)).symm)
  have apc1303:=fun (q794 q795 q813 q814 q815 q816 q817 q823 q824 q825:G)=>by
    exact ((apc1302 q794 q795 q794).symm).trans (apc1293 q794 q795 q794 q794 q794 q794 q794)
  exact (apc1303 x y ((x ◇ y) ◇ y) ((x ◇ y) ◇ y) ((x ◇ y) ◇ y) ((x ◇ y) ◇ y) ((x ◇ y) ◇ y) ((x ◇ y) ◇ y) ((x ◇ y) ◇ y) ((x ◇ y) ◇ y)).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_60536_to_60338 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_60536_to_60338
