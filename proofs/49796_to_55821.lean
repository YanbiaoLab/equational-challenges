-- Equation49796 → Equation55821
-- Recorded verdict: true
-- Premise: x * y = (y * (x * (z * x))) * x
-- Conclusion: x * (y * x) = (y * z) * (x * x)
-- Original submission SHA-256: 4542dc76e2aada74f9f150c99d011a71108c26bf6f0aa8acc8dbc0eba951ab37
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ (x ◇ (z ◇ x))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ x) = (y ◇ z) ◇ (x ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc0:=fun (q0 q1 q2:G)=>by
    exact ((cg (fun t => t ◇ q1) (cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) ((h q1 q0 q0).symm)))).symm).trans ((h q1 q2 (q0 ◇ (q1 ◇ (q0 ◇ q1)))).symm)
  have apc1:=fun (q0 q3 q1 q4:G)=>by
    exact (((cg (fun t => t ◇ q1) ((h (q1 ◇ (q4 ◇ q1)) q0 q3).symm)).symm).trans ((h q1 (q0 ◇ ((q1 ◇ (q4 ◇ q1)) ◇ (q3 ◇ (q1 ◇ (q4 ◇ q1))))) q4).symm)).symm
  have apc2:=fun (q5 q6 q7:G)=>by
    exact ((cg (fun t => t ◇ q6) (cg (fun t => q7 ◇ t) (apc1 q6 q5 q6 q5))).symm).trans (apc0 ((q6 ◇ (q5 ◇ q6)) ◇ (q5 ◇ (q6 ◇ (q5 ◇ q6)))) q6 q7)
  have apc3:=fun (q8 q9:G)=>by
    exact ((cg (fun t => t ◇ q8) (cg (fun t => q9 ◇ t) (cg (fun t => t ◇ q8) (apc2 q8 q8 q8)))).symm).trans (apc2 ((q8 ◇ (q8 ◇ q8)) ◇ q8) q8 q9)
  have apc5:=fun (q10 q5 q6 q7:G)=>by
    exact ((cg (fun t => t ◇ q6) (cg (fun t => q7 ◇ t) (cg (fun t => q6 ◇ t) (apc1 q10 q10 q6 q5)))).symm).trans (apc0 (q10 ◇ ((q6 ◇ (q5 ◇ q6)) ◇ (q10 ◇ (q6 ◇ (q5 ◇ q6))))) q6 q7)
  have apc6:=fun (q11 q12:G)=>by
    exact ((cg (fun t => t ◇ q11) (cg (fun t => q12 ◇ t) (cg (fun t => q11 ◇ t) (cg (fun t => t ◇ q11) (apc3 q11 q11))))).symm).trans (apc5 q11 (q11 ◇ q11) q11 q12)
  have apc10:=fun (q13 q14 q15 q16:G)=>by
    exact (((cg (fun t => t ◇ q15) (apc0 q13 (q15 ◇ (q16 ◇ q15)) q14)).symm).trans ((h q15 (q14 ◇ ((q15 ◇ (q16 ◇ q15)) ◇ ((q15 ◇ (q16 ◇ q15)) ◇ q13))) q16).symm)).symm
  have apc11:=fun (q17 q18:G)=>by
    exact ((cg (fun t => q17 ◇ t) (apc1 (q17 ◇ (q18 ◇ q17)) q17 q17 q18)).symm).trans (apc10 (q17 ◇ (q17 ◇ (q18 ◇ q17))) q17 q17 q18)
  have apc14:=fun (q19 q20:G)=>by
    exact ((((cg (fun t => q20 ◇ t) (cg (fun t => t ◇ q20) (cg (fun t => (q20 ◇ (q20 ◇ q19)) ◇ t) (cg (fun t => q20 ◇ t) (apc0 q19 q20 q19))))).trans (cg (fun t => q20 ◇ t) (apc0 q19 q20 (q20 ◇ (q20 ◇ q19))))).symm).trans ((((cg (fun t => q20 ◇ t) (cg (fun t => t ◇ q20) (cg (fun t => t ◇ (q20 ◇ ((q19 ◇ (q20 ◇ (q20 ◇ q19))) ◇ q20))) (cg (fun t => q20 ◇ t) (apc0 q19 q20 q19))))).symm).trans (apc11 q20 (q19 ◇ (q20 ◇ (q20 ◇ q19))))).trans (cg (fun t => t ◇ q20) (cg (fun t => t ◇ q20) (cg (fun t => q20 ◇ t) (apc0 q19 q20 q19)))))).symm
  have apc15:=fun (q21:G)=>by
    exact (((cg (fun t => q21 ◇ t) (apc6 q21 (q21 ◇ ((q21 ◇ q21) ◇ q21)))).symm).trans (apc11 q21 (q21 ◇ q21))).trans (cg (fun t => t ◇ q21) (apc3 q21 q21))
  have apc16:=fun (q22:G)=>by
    exact ((cg (fun t => t ◇ q22) (apc15 q22)).symm).trans (apc0 ((q22 ◇ q22) ◇ q22) q22 q22)
  have apc17:=fun (q23:G)=>by
    exact (((cg (fun t => t ◇ q23) (apc16 q23)).symm).trans ((((cg (fun t => t ◇ q23) (cg (fun t => t ◇ q23) (apc15 q23))).symm).trans (apc14 (q23 ◇ ((q23 ◇ q23) ◇ q23)) q23)).trans (cg (fun t => q23 ◇ t) (cg (fun t => q23 ◇ t) (apc15 q23))))).symm
  have apc18:=fun (q23 q21:G)=>by
    exact ((cg (fun t => q21 ◇ t) (apc17 q21)).symm).trans (apc15 q21)
  have apc32:=fun (q24 q25 q26 q27:G)=>by
    exact (((cg (fun t => t ◇ q27) ((h (q27 ◇ (q27 ◇ q26)) q24 q25).symm)).symm).trans (apc0 q26 q27 (q24 ◇ ((q27 ◇ (q27 ◇ q26)) ◇ (q25 ◇ (q27 ◇ (q27 ◇ q26))))))).symm
  have apc33:=fun (q28 q29:G)=>by
    exact ((cg (fun t => q29 ◇ t) (apc0 (q29 ◇ q28) q29 (q29 ◇ (q29 ◇ q28)))).symm).trans ((((cg (fun t => q29 ◇ t) (apc32 (q29 ◇ (q29 ◇ (q29 ◇ q28))) q29 q28 q29)).symm).trans (apc32 q29 (q29 ◇ (q29 ◇ q28)) (q29 ◇ q28) q29)).trans (cg (fun t => t ◇ q29) (apc0 q28 q29 q29)))
  have apc35:=fun (q19 q20 q28 q29:G)=>by
    exact (apc14 q19 q20).trans (apc33 q19 q20)
  have apc36:=fun (q30 q31:G)=>by
    exact ((cg (fun t => q31 ◇ t) (apc0 (q30 ◇ q31) q31 (q31 ◇ (q30 ◇ q31)))).symm).trans ((((cg (fun t => q31 ◇ t) (apc1 (q31 ◇ (q31 ◇ (q30 ◇ q31))) q31 q31 q30)).symm).trans (apc32 q31 (q31 ◇ (q30 ◇ q31)) (q30 ◇ q31) q31)).trans (apc35 (q30 ◇ q31) q31 (((q31 ◇ (q31 ◇ (q30 ◇ q31))) ◇ q31) ◇ q31) (((q31 ◇ (q31 ◇ (q30 ◇ q31))) ◇ q31) ◇ q31)))
  have apc38:=fun (q32 q33:G)=>by
    exact ((cg (fun t => t ◇ (q33 ◇ (q33 ◇ q32))) (apc0 q32 q33 (q33 ◇ (q33 ◇ q32)))).symm).trans (((cg (fun t => t ◇ (q33 ◇ (q33 ◇ q32))) (apc32 (q33 ◇ (q33 ◇ q32)) q32 q32 q33)).symm).trans (apc0 (q32 ◇ (q33 ◇ (q33 ◇ q32))) (q33 ◇ (q33 ◇ q32)) q33))
  have apc40:=fun (q34:G)=>by
    exact (((cg (fun t => t ◇ (q34 ◇ (q34 ◇ (q34 ◇ (q34 ◇ q34))))) (apc18 (q34 ◇ ((q34 ◇ q34) ◇ q34)) q34)).trans (cg (fun t => ((q34 ◇ q34) ◇ q34) ◇ t) (apc33 q34 q34))).symm).trans ((((cg (fun t => t ◇ (q34 ◇ (q34 ◇ (q34 ◇ (q34 ◇ q34))))) (cg (fun t => q34 ◇ t) (apc33 q34 q34))).symm).trans (apc38 (q34 ◇ (q34 ◇ q34)) q34)).trans ((cg (fun t => t ◇ q34) (apc33 q34 q34)).trans (apc16 q34)))
  have apc48:=fun (q35:G)=>by
    exact (((cg (fun t => t ◇ ((q35 ◇ q35) ◇ q35)) (cg (fun t => t ◇ ((q35 ◇ q35) ◇ q35)) (apc40 q35))).symm).trans (apc16 ((q35 ◇ q35) ◇ q35))).trans (apc40 q35)
  have apc49:=fun (q36:G)=>by
    exact (((cg (fun t => t ◇ q36) (apc48 q36)).symm).trans (apc3 q36 ((q36 ◇ q36) ◇ ((q36 ◇ q36) ◇ q36)))).symm
  have apc50:=fun (q37:G)=>by
    exact ((cg (fun t => t ◇ (q37 ◇ q37)) (apc49 q37)).symm).trans (apc0 q37 (q37 ◇ q37) q37)
  have apc51:=fun (q38:G)=>by
    exact (((((cg (fun t => ((q38 ◇ q38) ◇ q38) ◇ t) (cg (fun t => ((q38 ◇ q38) ◇ q38) ◇ t) (apc40 q38))).trans (cg (fun t => ((q38 ◇ q38) ◇ q38) ◇ t) (apc50 q38))).trans (apc40 q38)).symm).trans ((((cg (fun t => ((q38 ◇ q38) ◇ q38) ◇ t) (cg (fun t => ((q38 ◇ q38) ◇ q38) ◇ t) (cg (fun t => ((q38 ◇ q38) ◇ q38) ◇ t) (apc50 q38)))).symm).trans (apc33 (q38 ◇ q38) ((q38 ◇ q38) ◇ q38))).trans (cg (fun t => t ◇ ((q38 ◇ q38) ◇ q38)) (apc40 q38)))).symm
  have apc52:=fun (q39:G)=>by
    exact ((((cg (fun t => ((q39 ◇ q39) ◇ q39) ◇ t) (cg (fun t => ((q39 ◇ q39) ◇ q39) ◇ t) (apc50 q39))).trans (cg (fun t => ((q39 ◇ q39) ◇ q39) ◇ t) (apc40 q39))).trans (apc50 q39)).symm).trans ((((cg (fun t => ((q39 ◇ q39) ◇ q39) ◇ t) (cg (fun t => ((q39 ◇ q39) ◇ q39) ◇ t) (cg (fun t => ((q39 ◇ q39) ◇ q39) ◇ t) (apc51 q39)))).symm).trans (apc36 (q39 ◇ q39) ((q39 ◇ q39) ◇ q39))).trans ((cg (fun t => t ◇ ((q39 ◇ q39) ◇ q39)) (apc40 q39)).trans (apc51 q39)))
  have apc53:=fun (q36 q38:G)=>by
    exact (((cg (fun t => q36 ◇ t) (apc51 q36)).symm).trans (apc49 q36)).trans (apc52 q36)
  have apc54:=fun (q8 q9 q39:G)=>by
    exact ((cg (fun t => t ◇ q8) (cg (fun t => q9 ◇ t) (apc52 q8))).symm).trans (apc3 q8 q9)
  have apc56:=fun (q40 q41:G)=>by
    exact ((cg (fun t => t ◇ (q40 ◇ q40)) (cg (fun t => q41 ◇ t) (apc51 q40))).symm).trans (apc0 q40 (q40 ◇ q40) q41)
  have apc57:=fun (q42:G)=>by
    exact (((cg (fun t => t ◇ (q42 ◇ q42)) (apc53 q42 q42)).symm).trans (apc56 q42 q42)).trans (apc52 q42)
  have apc58:=fun (q43 q44:G)=>by
    exact ((cg (fun t => t ◇ q44) (apc56 q44 q43)).symm).trans (apc54 q44 (q43 ◇ (q44 ◇ q44)) q43)
  have apc61:=fun (q19 q20 q28 q29 q39:G)=>by
    exact (apc35 q19 q20 q19 q19).trans (apc52 q20)
  have apc63:=fun (q45 q46:G)=>by
    exact ((cg (fun t => t ◇ (q46 ◇ q46)) (apc56 q46 q45)).symm).trans (apc56 q46 (q45 ◇ (q46 ◇ q46)))
  have apc74:=fun (q47 q48:G)=>by
    exact ((cg (fun t => t ◇ q48) (cg (fun t => (q48 ◇ q48) ◇ t) (cg (fun t => q47 ◇ t) (apc57 q48)))).symm).trans ((((cg (fun t => t ◇ q48) (apc58 q47 (q48 ◇ q48))).symm).trans (apc54 q48 (((q48 ◇ q48) ◇ (q48 ◇ q48)) ◇ q47) q47)).trans (cg (fun t => q48 ◇ t) (cg (fun t => t ◇ q47) (apc57 q48))))
  have apc75:=fun (q49 q50 q51:G)=>by
    exact (((cg (fun t => t ◇ q51) (cg (fun t => t ◇ q49) (apc52 q51))).symm).trans ((((cg (fun t => t ◇ q51) ((h ((q51 ◇ q51) ◇ q51) q49 q50).symm)).symm).trans (apc3 q51 (q49 ◇ (((q51 ◇ q51) ◇ q51) ◇ (q50 ◇ ((q51 ◇ q51) ◇ q51)))))).trans ((cg (fun t => q51 ◇ t) (cg (fun t => q49 ◇ t) (cg (fun t => ((q51 ◇ q51) ◇ q51) ◇ t) (cg (fun t => q50 ◇ t) (apc52 q51))))).trans (cg (fun t => q51 ◇ t) (cg (fun t => q49 ◇ t) (cg (fun t => t ◇ (q50 ◇ (q51 ◇ q51))) (apc52 q51))))))).symm
  have apc76:=fun (q52 q53:G)=>by
    exact ((cg (fun t => t ◇ (q52 ◇ (q53 ◇ q53))) (apc74 q52 q53)).symm).trans ((((cg (fun t => t ◇ (q52 ◇ (q53 ◇ q53))) (apc75 (q52 ◇ (q53 ◇ q53)) q52 q53)).symm).trans ((h (q52 ◇ (q53 ◇ q53)) q53 (q53 ◇ q53)).symm)).trans (apc54 q53 q52 ((q52 ◇ (q53 ◇ q53)) ◇ q53)))
  have apc81:=fun (q54 q55:G)=>by
    exact (((cg (fun t => (q55 ◇ (q55 ◇ q54)) ◇ t) (cg (fun t => t ◇ q55) (apc53 (q55 ◇ (q55 ◇ q54)) ((q55 ◇ (q55 ◇ q54)) ◇ ((q55 ◇ (q55 ◇ q54)) ◇ (q55 ◇ (q55 ◇ q54))))))).trans (cg (fun t => (q55 ◇ (q55 ◇ q54)) ◇ t) (apc0 q54 q55 (q55 ◇ (q55 ◇ q54))))).symm).trans ((((cg (fun t => (q55 ◇ (q55 ◇ q54)) ◇ t) (apc32 ((q55 ◇ (q55 ◇ q54)) ◇ (q55 ◇ (q55 ◇ q54))) (q55 ◇ (q55 ◇ q54)) q54 q55)).symm).trans (apc75 q55 (q55 ◇ (q55 ◇ q54)) (q55 ◇ (q55 ◇ q54)))).trans ((cg (fun t => t ◇ (q55 ◇ (q55 ◇ q54))) (apc0 q54 q55 (q55 ◇ (q55 ◇ q54)))).trans (apc38 q54 q55)))
  have apc82:=fun (q56 q57:G)=>by
    exact (((apc61 q56 q57 (((q57 ◇ (q57 ◇ q56)) ◇ q57) ◇ q57) (((q57 ◇ (q57 ◇ q56)) ◇ q57) ◇ q57) (((q57 ◇ (q57 ◇ q56)) ◇ q57) ◇ q57)).symm).trans (((cg (fun t => t ◇ q57) (apc81 q56 q57)).symm).trans (apc0 (q57 ◇ q56) q57 (q57 ◇ (q57 ◇ q56))))).symm
  have apc83:=fun (q32 q33 q56 q57:G)=>by
    exact (((cg (fun t => t ◇ (q33 ◇ (q33 ◇ q32))) (apc82 q32 q33)).symm).trans (apc38 q32 q33)).symm
  have apc97:=fun (q58 q59:G)=>by
    exact ((((((cg (fun t => t ◇ q59) (cg (fun t => t ◇ ((q59 ◇ q59) ◇ ((q59 ◇ q59) ◇ q58))) (apc57 q59))).trans (cg (fun t => t ◇ q59) (apc82 q58 (q59 ◇ q59)))).trans (cg (fun t => t ◇ q59) (apc57 q59))).trans (apc52 q59)).symm).trans (((cg (fun t => t ◇ q59) (apc83 q58 (q59 ◇ q59) q58 q58)).symm).trans (apc54 q59 ((q59 ◇ q59) ◇ ((q59 ◇ q59) ◇ q58)) q58))).symm
  have apc114:=fun (q60 q61 q62:G)=>by
    exact (((cg (fun t => t ◇ q62) (cg (fun t => t ◇ q61) (apc52 q62))).symm).trans ((((cg (fun t => t ◇ q62) (apc0 q60 ((q62 ◇ q62) ◇ q62) q61)).symm).trans (apc3 q62 (q61 ◇ (((q62 ◇ q62) ◇ q62) ◇ (((q62 ◇ q62) ◇ q62) ◇ q60))))).trans ((cg (fun t => q62 ◇ t) (cg (fun t => q61 ◇ t) (cg (fun t => ((q62 ◇ q62) ◇ q62) ◇ t) (cg (fun t => t ◇ q60) (apc52 q62))))).trans (cg (fun t => q62 ◇ t) (cg (fun t => q61 ◇ t) (cg (fun t => t ◇ ((q62 ◇ q62) ◇ q60)) (apc52 q62))))))).symm
  have apc115:=fun (q63 q64:G)=>by
    exact (((((((cg (fun t => t ◇ ((q64 ◇ q64) ◇ ((q64 ◇ q64) ◇ q63))) (cg (fun t => t ◇ q64) (apc82 q63 (q64 ◇ q64)))).trans (cg (fun t => t ◇ ((q64 ◇ q64) ◇ ((q64 ◇ q64) ◇ q63))) (cg (fun t => t ◇ q64) (apc57 q64)))).trans (cg (fun t => t ◇ ((q64 ◇ q64) ◇ ((q64 ◇ q64) ◇ q63))) (apc52 q64))).trans (apc82 q63 (q64 ◇ q64))).trans (apc57 q64)).symm).trans (((cg (fun t => t ◇ ((q64 ◇ q64) ◇ ((q64 ◇ q64) ◇ q63))) (apc114 q63 ((q64 ◇ q64) ◇ ((q64 ◇ q64) ◇ q63)) q64)).symm).trans (apc54 ((q64 ◇ q64) ◇ ((q64 ◇ q64) ◇ q63)) q64 q63))).symm
  have apc116:=fun (q65 q66:G)=>by
    exact (((apc115 q65 q66).symm).trans (apc58 ((q66 ◇ q66) ◇ q65) q66)).symm
  have apc117:=fun (q67 q68:G)=>by
    exact ((cg (fun t => q68 ◇ t) (apc63 q67 q68)).symm).trans (apc116 q67 q68)
  have apc118:=fun (q69 q70:G)=>by
    exact ((cg (fun t => (q70 ◇ q70) ◇ t) (apc56 q70 q69)).symm).trans (((cg (fun t => t ◇ ((q69 ◇ (q70 ◇ q70)) ◇ (q70 ◇ q70))) (apc117 q69 q70)).symm).trans (apc76 (q69 ◇ (q70 ◇ q70)) q70))
  have apc119:=fun (q69 q70 q58 q59:G)=>by
    exact ((cg (fun t => q59 ◇ t) (apc118 q58 q59)).symm).trans (apc97 q58 q59)
  have apc120:=fun (q71 q72:G)=>by
    exact (((apc118 (q72 ◇ (q71 ◇ q71)) q71).trans (cg (fun t => q71 ◇ t) (apc56 q71 q72))).symm).trans ((((cg (fun t => (q71 ◇ q71) ◇ t) (cg (fun t => (q71 ◇ q71) ◇ t) (cg (fun t => q72 ◇ t) (apc57 q71)))).symm).trans (apc119 q71 q71 q72 (q71 ◇ q71))).trans (apc57 q71))
  have apc124:=fun (q73 q74:G)=>by
    exact (((cg (fun t => (q73 ◇ q73) ◇ t) (cg (fun t => t ◇ q74) (apc57 q73))).symm).trans ((((cg (fun t => t ◇ (((q73 ◇ q73) ◇ (q73 ◇ q73)) ◇ q74)) (apc57 q73)).symm).trans (apc118 q74 (q73 ◇ q73))).trans (cg (fun t => (q73 ◇ q73) ◇ t) (cg (fun t => q74 ◇ t) (apc57 q73))))).symm
  have apc125:=fun (q71 q72 q52 q53:G)=>by
    exact ((apc124 q53 q52).symm).trans (((cg (fun t => t ◇ (q52 ◇ (q53 ◇ q53))) (apc120 q53 q52)).symm).trans (apc76 q52 q53))
  have apc126:=fun (q75 q76:G)=>by
    exact ((apc125 ((q76 ◇ q76) ◇ ((q76 ◇ q76) ◇ (q76 ◇ q75))) ((q76 ◇ q76) ◇ ((q76 ◇ q76) ◇ (q76 ◇ q75))) (q76 ◇ q75) q76).symm).trans ((((cg (fun t => (q76 ◇ q76) ◇ t) (cg (fun t => (q76 ◇ q76) ◇ t) (apc125 q75 q75 q75 q76))).symm).trans (apc82 ((q76 ◇ q76) ◇ q75) (q76 ◇ q76))).trans (apc57 q76))
  have apc127:=fun (q77 q78:G)=>by
    exact (((((cg (fun t => (q77 ◇ q77) ◇ t) (cg (fun t => t ◇ q78) (apc57 q77))).trans (apc126 q78 (q77 ◇ q77))).trans (apc57 q77)).symm).trans (((cg (fun t => t ◇ (((q77 ◇ q77) ◇ (q77 ◇ q77)) ◇ q78)) (apc57 q77)).symm).trans (apc125 q77 q77 q78 (q77 ◇ q77)))).symm
  have apc129:=fun (q79 q80:G)=>by
    exact (((apc127 q79 q80).symm).trans (((cg (fun t => t ◇ q80) (apc127 q79 (q80 ◇ (q79 ◇ q80)))).symm).trans ((h q80 (q79 ◇ q79) q79).symm))).symm
  have apc130:=fun (q81 q82:G)=>by
    exact ((((cg (fun t => t ◇ q81) (apc129 q81 q82)).trans (apc127 q81 q81)).symm).trans (((cg (fun t => t ◇ q81) (cg (fun t => q82 ◇ t) (apc129 q81 q81))).symm).trans ((h q81 q82 q81).symm))).symm
  have apc131:=fun (q83 q84:G)=>by
    exact (((((cg (fun t => t ◇ q83) (cg (fun t => q84 ◇ t) (cg (fun t => q83 ◇ t) (apc127 q83 q83)))).trans (cg (fun t => t ◇ q83) (cg (fun t => q84 ◇ t) (apc130 q83 (q83 ◇ q83))))).trans (cg (fun t => t ◇ q83) (apc130 q84 (q83 ◇ q83)))).trans (apc127 q84 q83)).symm).trans ((((cg (fun t => t ◇ q83) (cg (fun t => q84 ◇ t) (cg (fun t => q83 ◇ t) (cg (fun t => t ◇ q83) (apc129 q83 (q83 ◇ (q83 ◇ q83))))))).symm).trans (apc5 (q83 ◇ q83) q83 q83 q84)).trans (apc130 q83 q84))
  have apc132:=fun (q85 q86:G)=>by
    exact ((h q86 q85 q85).trans (apc130 (q85 ◇ (q86 ◇ (q85 ◇ q86))) q86)).trans (((((((cg (fun t => t ◇ (q85 ◇ (q86 ◇ (q85 ◇ q86)))) (cg (fun t => q85 ◇ t) (cg (fun t => q86 ◇ t) (apc130 q85 q86)))).trans (cg (fun t => (q85 ◇ (q86 ◇ (q85 ◇ q85))) ◇ t) (cg (fun t => q85 ◇ t) (cg (fun t => q86 ◇ t) (apc130 q85 q86))))).trans (cg (fun t => t ◇ (q85 ◇ (q86 ◇ (q85 ◇ q85)))) (cg (fun t => q85 ◇ t) (apc130 q86 (q85 ◇ q85))))).trans (cg (fun t => (q85 ◇ (q86 ◇ q86)) ◇ t) (cg (fun t => q85 ◇ t) (apc130 q86 (q85 ◇ q85))))).trans (cg (fun t => t ◇ (q85 ◇ (q86 ◇ q86))) (apc130 q85 (q86 ◇ q86)))).trans (cg (fun t => (q85 ◇ q85) ◇ t) (apc130 q85 (q86 ◇ q86)))).trans (apc127 q85 (q85 ◇ q85)))
  exact (calc
    (x ◇ (y ◇ x))=((y ◇ x) ◇ (y ◇ x)):=apc132 (y ◇ x) x
    _=((y ◇ z) ◇ (y ◇ z)):=apc131 (y ◇ z) (y ◇ x)
    _=((y ◇ z) ◇ (x ◇ x)):=(apc130 (y ◇ z) (x ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49796_to_55821 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49796_to_55821
