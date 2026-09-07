-- Equation2923 → Equation17160
-- Recorded verdict: true
-- Premise: x = ((y * (x * z)) * y) * x
-- Conclusion: x = (x * y) * (z * (w * (z * x)))
-- Original submission SHA-256: 7fe26b262ef19ee1761c048b445d0cd6df7b8c29bff7ac8d3a0ceba69f0c4fdf
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ (x ◇ z)) ◇ y) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ y) ◇ (z ◇ (w ◇ (z ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc2:=fun (q0 q1 q2 q3:G)=>by
    exact ((cg (fun t => t ◇ ((q0 ◇ (q3 ◇ q1)) ◇ q0)) (cg (fun t => t ◇ q2) (cg (fun t => q2 ◇ t) ((h q3 q0 q1).symm)))).symm).trans ((h ((q0 ◇ (q3 ◇ q1)) ◇ q0) q2 q3).symm)
  have apc3:=fun (q4 q5:G)=>by
    exact ((cg (fun t => t ◇ q5) (apc2 q5 q4 (q5 ◇ (q5 ◇ q4)) q5)).symm).trans ((h q5 ((q5 ◇ (q5 ◇ q4)) ◇ q5) (q5 ◇ q4)).symm)
  have apc4:=fun (q0 q1 q6 q3:G)=>by
    exact ((cg (fun t => t ◇ q6) (cg (fun t => t ◇ ((q0 ◇ ((q6 ◇ q3) ◇ q1)) ◇ q0)) ((h (q6 ◇ q3) q0 q1).symm))).symm).trans ((h q6 ((q0 ◇ ((q6 ◇ q3) ◇ q1)) ◇ q0) q3).symm)
  have apc5:=fun (q7 q4 q8 q5 q9:G)=>by
    exact ((cg (fun t => t ◇ ((q8 ◇ q5) ◇ q8)) (cg (fun t => t ◇ q9) (cg (fun t => q9 ◇ t) (apc2 q7 q4 q8 q5)))).symm).trans ((h ((q8 ◇ q5) ◇ q8) q9 ((q7 ◇ (q5 ◇ q4)) ◇ q7)).symm)
  have apc6:=fun (q10 q11 q12 q13 q14:G)=>by
    exact ((cg (fun t => t ◇ ((q12 ◇ (q14 ◇ q13)) ◇ q12)) (cg (fun t => t ◇ ((q10 ◇ (q14 ◇ q11)) ◇ q10)) ((h q14 q10 q11).symm))).symm).trans (apc2 q12 q13 ((q10 ◇ (q14 ◇ q11)) ◇ q10) q14)
  have apc8:=fun (q10 q11 q12 q13:G)=>by
    exact (((apc5 q10 q11 q12 q13 q10).symm).trans (((cg (fun t => ((q10 ◇ ((q10 ◇ (q13 ◇ q11)) ◇ q10)) ◇ q10) ◇ t) (cg (fun t => t ◇ q12) (cg (fun t => q12 ◇ t) ((h q13 q10 q11).symm)))).symm).trans (apc2 q12 q13 q10 ((q10 ◇ (q13 ◇ q11)) ◇ q10)))).symm
  have apc10:=fun (q15 q16 q17 q18 q19:G)=>by
    exact ((cg (fun t => t ◇ ((q18 ◇ q19) ◇ q18)) (cg (fun t => t ◇ ((q15 ◇ q19) ◇ q15)) (apc2 q16 q17 q15 q19))).symm).trans (apc5 q16 q17 q18 q19 ((q15 ◇ q19) ◇ q15))
  have apc12:=fun (q20 q21 q22 q23 q24:G)=>by
    exact ((cg (fun t => t ◇ (q24 ◇ q22)) (cg (fun t => ((q24 ◇ q22) ◇ q24) ◇ t) (cg (fun t => t ◇ q23) (cg (fun t => q23 ◇ t) (apc2 q20 q21 q24 q22))))).symm).trans (apc4 q23 ((q20 ◇ (q22 ◇ q21)) ◇ q20) (q24 ◇ q22) q24)
  have apc17:=fun (q25 q26 q27 q28 q29 q30:G)=>by
    exact (((cg (fun t => ((q30 ◇ ((q27 ◇ q28) ◇ q27)) ◇ q30) ◇ t) (cg (fun t => t ◇ q29) (cg (fun t => q29 ◇ t) (apc2 q25 q26 q27 q28)))).symm).trans (apc2 q29 ((q25 ◇ (q28 ◇ q26)) ◇ q25) q30 ((q27 ◇ q28) ◇ q27))).trans (cg (fun t => t ◇ q29) (cg (fun t => q29 ◇ t) (apc2 q25 q26 q27 q28)))
  have apc22:=fun (q31 q32 q33 q34 q35 q36:G)=>by
    exact ((cg (fun t => t ◇ (q35 ◇ ((q31 ◇ (q35 ◇ q32)) ◇ q31))) (cg (fun t => t ◇ q36) (cg (fun t => q36 ◇ t) (apc6 q31 q32 q33 q34 q35)))).symm).trans ((h (q35 ◇ ((q31 ◇ (q35 ◇ q32)) ◇ q31)) q36 ((q33 ◇ (q35 ◇ q34)) ◇ q33)).symm)
  have apc24:=fun (q37 q38 q39 q40 q41:G)=>by
    exact ((cg (fun t => t ◇ (q41 ◇ (((q37 ◇ (q39 ◇ q38)) ◇ q37) ◇ q39))) (cg (fun t => t ◇ q40) (cg (fun t => q40 ◇ t) (apc8 q37 q38 q41 q39)))).symm).trans ((h (q41 ◇ (((q37 ◇ (q39 ◇ q38)) ◇ q37) ◇ q39)) q40 q41).symm)
  have apc25:=fun (q42 q43 q44:G)=>by
    exact (((cg (fun t => ((q43 ◇ ((q44 ◇ q42) ◇ q44)) ◇ q43) ◇ t) (cg (fun t => q44 ◇ t) (apc3 q42 q42))).symm).trans (apc24 q42 q42 q42 q43 q44)).trans (cg (fun t => q44 ◇ t) (apc3 q42 q42))
  have apc26:=fun (q45 q46 q47 q48:G)=>by
    exact (((apc25 q47 q45 q48).symm).trans (((cg (fun t => ((q45 ◇ ((q48 ◇ q47) ◇ q48)) ◇ q45) ◇ t) (cg (fun t => q48 ◇ t) ((h q47 q45 q46).symm))).symm).trans (apc24 q45 q46 q47 q45 q48))).symm
  have apc45:=fun (q49 q50 q51 q52 q53:G)=>by
    exact ((cg (fun t => t ◇ (q53 ◇ q52)) (cg (fun t => t ◇ (((q50 ◇ (q52 ◇ q51)) ◇ q50) ◇ ((q49 ◇ q52) ◇ q49))) (apc10 q49 q50 q51 q53 q52))).symm).trans ((h (q53 ◇ q52) (((q50 ◇ (q52 ◇ q51)) ◇ q50) ◇ ((q49 ◇ q52) ◇ q49)) q53).symm)
  have apc48:=fun (q54 q55 q56 q57 q58 q59:G)=>by
    exact ((cg (fun t => t ◇ ((q57 ◇ ((((q54 ◇ (q56 ◇ q55)) ◇ q54) ◇ q56) ◇ q58)) ◇ q57)) (apc8 q54 q55 q59 q56)).symm).trans (apc2 q57 q58 q59 (((q54 ◇ (q56 ◇ q55)) ◇ q54) ◇ q56))
  have apc49:=fun (q60 q61 q62 q63 q64:G)=>by
    exact (((apc2 q63 q64 q60 q62).symm).trans (((cg (fun t => ((q60 ◇ q62) ◇ q60) ◇ t) (cg (fun t => t ◇ q63) (cg (fun t => q63 ◇ t) (cg (fun t => t ◇ q64) ((h q62 q60 q61).symm))))).symm).trans (apc48 q60 q61 q62 q63 q64 q60))).symm
  have apc53:=fun (q65 q66 q67:G)=>by
    exact (((apc22 q65 q66 q65 q65 q67 q65).symm).trans (((cg (fun t => ((q65 ◇ ((q65 ◇ (q67 ◇ q65)) ◇ q65)) ◇ q65) ◇ t) (cg (fun t => t ◇ ((q65 ◇ (q67 ◇ q66)) ◇ q65)) ((h q67 q65 q66).symm))).symm).trans (apc5 q65 q65 ((q65 ◇ (q67 ◇ q66)) ◇ q65) q67 q65))).symm
  have apc54:=fun (q68 q69 q70 q71 q72:G)=>by
    exact (((((cg (fun t => t ◇ ((q71 ◇ ((((q68 ◇ (q70 ◇ q69)) ◇ q68) ◇ q70) ◇ q72)) ◇ q71)) (cg (fun t => t ◇ q70) (apc49 q68 q69 q70 q71 q72))).trans (cg (fun t => (((q71 ◇ (q70 ◇ q72)) ◇ q71) ◇ q70) ◇ t) (apc49 q68 q69 q70 q71 q72))).trans (apc53 q71 q72 q70)).symm).trans ((((cg (fun t => t ◇ ((q71 ◇ ((((q68 ◇ (q70 ◇ q69)) ◇ q68) ◇ q70) ◇ q72)) ◇ q71)) (apc26 q68 q69 q70 ((q71 ◇ ((((q68 ◇ (q70 ◇ q69)) ◇ q68) ◇ q70) ◇ q72)) ◇ q71))).symm).trans (apc53 q71 q72 (((q68 ◇ (q70 ◇ q69)) ◇ q68) ◇ q70))).trans (cg (fun t => (((q68 ◇ (q70 ◇ q69)) ◇ q68) ◇ q70) ◇ t) (apc49 q68 q69 q70 q71 q72)))).symm
  have apc71:=fun (q73 q74 q75 q76:G)=>by
    exact ((cg (fun t => t ◇ ((q76 ◇ ((q74 ◇ (q74 ◇ q73)) ◇ q74)) ◇ q76)) (apc17 q74 q73 (q74 ◇ (q74 ◇ q73)) q74 q75 q73)).symm).trans (apc10 q75 q73 (q74 ◇ (q74 ◇ q73)) q76 ((q74 ◇ (q74 ◇ q73)) ◇ q74))
  have apc72:=fun (q77 q78 q79 q80:G)=>by
    exact (((cg (fun t => t ◇ (q80 ◇ (q79 ◇ (q79 ◇ q77)))) (cg (fun t => ((q80 ◇ (q79 ◇ (q79 ◇ q77))) ◇ q80) ◇ t) (apc71 q77 q79 q77 q78))).trans (cg (fun t => t ◇ (q80 ◇ (q79 ◇ (q79 ◇ q77)))) (apc2 q78 q79 q80 (q79 ◇ (q79 ◇ q77))))).symm).trans (((cg (fun t => t ◇ (q80 ◇ (q79 ◇ (q79 ◇ q77)))) (cg (fun t => ((q80 ◇ (q79 ◇ (q79 ◇ q77))) ◇ q80) ◇ t) (cg (fun t => t ◇ ((q78 ◇ ((q79 ◇ (q79 ◇ q77)) ◇ q79)) ◇ q78)) (apc71 q77 q79 q78 q77)))).symm).trans (apc12 q77 q79 (q79 ◇ (q79 ◇ q77)) ((q78 ◇ ((q79 ◇ (q79 ◇ q77)) ◇ q79)) ◇ q78) q80))
  have apc73:=fun (q81 q82 q83 q84 q85:G)=>by
    exact ((((cg (fun t => t ◇ (q85 ◇ (((q81 ◇ (q83 ◇ q82)) ◇ q81) ◇ (((q81 ◇ (q83 ◇ q82)) ◇ q81) ◇ q83)))) (cg (fun t => t ◇ q84) (cg (fun t => q84 ◇ t) (apc54 q81 q82 q83 q81 q82)))).trans (cg (fun t => ((q84 ◇ (q83 ◇ ((q81 ◇ (q83 ◇ q82)) ◇ q81))) ◇ q84) ◇ t) (cg (fun t => q85 ◇ t) (apc26 q81 q82 q83 ((q81 ◇ (q83 ◇ q82)) ◇ q81))))).trans (cg (fun t => ((q84 ◇ (q83 ◇ ((q81 ◇ (q83 ◇ q82)) ◇ q81))) ◇ q84) ◇ t) (apc26 q81 q82 q83 q85))).symm).trans ((((cg (fun t => t ◇ (q85 ◇ (((q81 ◇ (q83 ◇ q82)) ◇ q81) ◇ (((q81 ◇ (q83 ◇ q82)) ◇ q81) ◇ q83)))) (cg (fun t => t ◇ q84) (cg (fun t => q84 ◇ t) (cg (fun t => t ◇ ((q81 ◇ (q83 ◇ q82)) ◇ q81)) (cg (fun t => ((q81 ◇ (q83 ◇ q82)) ◇ q81) ◇ t) ((h q83 q81 q82).symm)))))).symm).trans (apc72 q83 q84 ((q81 ◇ (q83 ◇ q82)) ◇ q81) q85)).trans ((cg (fun t => q85 ◇ t) (apc26 q81 q82 q83 ((q81 ◇ (q83 ◇ q82)) ◇ q81))).trans (apc26 q81 q82 q83 q85)))
  have apc74:=fun (q86 q87:G)=>by
    exact ((cg (fun t => t ◇ ((q87 ◇ q86) ◇ q87)) (apc73 q86 q86 q86 q86 (q86 ◇ q86))).symm).trans (apc10 q86 q86 ((q86 ◇ (q86 ◇ q86)) ◇ q86) q87 q86)
  have apc75:=fun (q88 q89:G)=>by
    exact ((cg (fun t => t ◇ (q89 ◇ q88)) (cg (fun t => ((q89 ◇ q88) ◇ q89) ◇ t) (apc73 q88 q88 q88 q88 (q88 ◇ q88)))).symm).trans (apc45 q88 q88 ((q88 ◇ (q88 ◇ q88)) ◇ q88) q88 q89)
  have apc76:=fun (q90:G)=>by
    exact ((cg (fun t => t ◇ (q90 ◇ q90)) (apc74 q90 q90)).symm).trans (apc75 q90 q90)
  have apc79:=fun (q91 q92:G)=>by
    exact ((cg (fun t => t ◇ (q92 ◇ q92)) (apc2 q91 q92 q92 q92)).symm).trans (((cg (fun t => t ◇ (q92 ◇ q92)) (cg (fun t => ((q92 ◇ q92) ◇ q92) ◇ t) (cg (fun t => t ◇ q91) (cg (fun t => q91 ◇ t) (apc76 q92))))).symm).trans (apc4 q91 (q92 ◇ q92) (q92 ◇ q92) q92))
  have apc80:=fun (q93:G)=>by
    exact ((cg (fun t => t ◇ (q93 ◇ q93)) (apc76 (q93 ◇ q93))).symm).trans (apc79 ((q93 ◇ q93) ◇ (q93 ◇ q93)) q93)
  have apc81:=fun (q94:G)=>by
    exact ((cg (fun t => t ◇ q94) (apc80 q94)).symm).trans ((h q94 (q94 ◇ q94) q94).symm)
  have apc83:=fun (q95 q96:G)=>by
    exact ((cg (fun t => t ◇ q95) (apc81 (q95 ◇ q96))).symm).trans ((h q95 (q95 ◇ q96) q96).symm)
  have apc84:=fun (x y z q95 q96:G)=>by
    exact ((h x y x).trans (cg (fun t => t ◇ x) (apc83 y (x ◇ x)))).symm
  exact (calc
    x=x:=rfl
    _=((x ◇ y) ◇ (z ◇ (w ◇ (z ◇ x)))):=(((((cg (fun t => (x ◇ y) ◇ t) (cg (fun t => z ◇ t) (cg (fun t => w ◇ t) (apc84 x z (z ◇ x) (z ◇ x) (z ◇ x))))).trans (cg (fun t => (x ◇ y) ◇ t) (cg (fun t => z ◇ t) (apc84 x w (w ◇ x) (w ◇ x) (w ◇ x))))).trans (cg (fun t => t ◇ (z ◇ x)) (apc84 y x (x ◇ y) (x ◇ y) (x ◇ y)))).trans (cg (fun t => y ◇ t) (apc84 x z (z ◇ x) (z ◇ x) (z ◇ x)))).trans (apc84 x y (y ◇ x) (y ◇ x) (y ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_2923_to_17160 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_2923_to_17160
