-- Equation19010 → Equation42551
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ ((z ◇ x) ◇ (y ◇ z))
-- Conclusion: x ◇ x = y ◇ (z ◇ ((y ◇ x) ◇ z))
-- Original submission SHA-256: 27e3641f59dca573122a32eb545a19153d5f6022931ba16a36bb702adaf9be2b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ ((z ◇ x) ◇ (y ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (z ◇ ((y ◇ x) ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc0:=fun (x y z:G)=>by
    exact ((h x y z).symm).trans (h x x x)
  have apc1:=fun (x y z:G)=>by
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2:=fun (q0 q1 q2 q3:G)=>by
    exact ((cg (fun t => ((q1 ◇ q0) ◇ q3) ◇ t) (cg (fun t => (((q2 ◇ q0) ◇ (q1 ◇ q2)) ◇ q3) ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h q3 (q1 ◇ q0) ((q2 ◇ q0) ◇ (q1 ◇ q2))).symm)
  have apc3:=fun (q0 q1 q2 q4:G)=>by
    exact ((cg (fun t => (q4 ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))) ◇ t) (cg (fun t => t ◇ (q4 ◇ (q1 ◇ q0))) ((h q0 q1 q2).symm))).symm).trans ((h ((q2 ◇ q0) ◇ (q1 ◇ q2)) q4 (q1 ◇ q0)).symm)
  have apc4:=fun (q5 q6 q7:G)=>by
    exact ((cg (fun t => t ◇ (q5 ◇ ((q6 ◇ q5) ◇ (q6 ◇ q5)))) ((h q5 q6 q7).symm)).symm).trans (apc3 q5 q6 q7 (q6 ◇ q5))
  have apc5:=fun (q5 q6 q7:G)=>by
    exact ((apc4 q5 q6 q7).symm).trans (apc4 q5 q6 q5)
  have apc6:=fun (x y z q5 q6 q7:G)=>by
    exact ((h x y x).trans (cg (fun t => (y ◇ x) ◇ t) (apc5 x y x))).symm
  have apc8:=fun (q5 q6 q7:G)=>by
    exact (apc4 q5 q6 q5).trans (apc5 q5 q6 q5)
  have apc9:=fun (q8 q9 q10:G)=>by
    exact ((cg (fun t => t ◇ q8) (cg (fun t => t ◇ q10) (apc5 q8 q9 q8))).symm).trans (((cg (fun t => (((q8 ◇ q8) ◇ (q9 ◇ q8)) ◇ q10) ◇ t) ((h q8 q9 q8).symm)).symm).trans (apc5 q10 (q9 ◇ q8) ((q8 ◇ q8) ◇ (q9 ◇ q8))))
  have apc10:=fun (q11 q12 q13 q14:G)=>by
    exact ((cg (fun t => ((q12 ◇ q13) ◇ q14) ◇ t) (apc5 q11 q12 q13)).symm).trans (apc5 q14 (q13 ◇ q11) (q12 ◇ q13))
  have apc11:=fun (q11 q12 q13 q15:G)=>by
    exact (((cg (fun t => t ◇ (q15 ◇ (q13 ◇ q11))) (apc5 q11 q12 q13)).symm).trans (apc5 (q12 ◇ q13) q15 (q13 ◇ q11))).symm
  have apc12:=fun (q11 q12 q13 q15:G)=>by
    exact (((apc11 q11 q12 q13 q15).symm).trans (apc11 q12 q12 q13 q15)).symm
  have apc18:=fun (q16 q6 q7:G)=>by
    exact ((cg (fun t => (((q6 ◇ q16) ◇ q16) ◇ ((q7 ◇ (q6 ◇ q16)) ◇ (q6 ◇ q7))) ◇ t) ((h q16 q6 (q6 ◇ q16)).symm)).symm).trans (apc3 (q6 ◇ q16) q6 q7 ((q6 ◇ q16) ◇ q16))
  have apc19:=fun (q17 q18:G)=>by
    exact ((cg (fun t => t ◇ q18) (apc5 q18 (q18 ◇ (q17 ◇ q18)) (q17 ◇ q18))).symm).trans (apc18 q18 q17 q18)
  have apc20:=fun (q19 q17 q18:G)=>by
    exact ((((cg (fun t => t ◇ q19) (apc10 (q17 ◇ q19) q17 q19 q19)).trans (apc19 q17 q19)).symm).trans (((cg (fun t => t ◇ q19) (cg (fun t => ((q17 ◇ q19) ◇ q19) ◇ t) (apc5 (q17 ◇ q19) q17 q18))).symm).trans (apc18 q19 q17 q18))).symm
  have apc21:=fun (q20 q21 q22:G)=>by
    exact ((cg (fun t => t ◇ (q22 ◇ (q21 ◇ q20))) (apc5 q20 q22 q21)).symm).trans (apc20 q21 q22 (q21 ◇ q20))
  have apc25:=fun (q23 q24:G)=>by
    exact ((cg (fun t => (q24 ◇ ((q23 ◇ q23) ◇ (q23 ◇ q23))) ◇ t) (cg (fun t => t ◇ (q24 ◇ (q23 ◇ q23))) (apc1 q23 q23 q23))).symm).trans ((h ((q23 ◇ q23) ◇ (q23 ◇ q23)) q24 (q23 ◇ q23)).symm)
  have apc26:=fun (q25 q26 q27:G)=>by
    exact ((apc10 q25 q25 (q26 ◇ (q25 ◇ q25)) q27).symm).trans (((cg (fun t => ((q25 ◇ (q26 ◇ (q25 ◇ q25))) ◇ q27) ◇ t) (apc25 q25 q26)).symm).trans (apc5 q27 (q26 ◇ ((q25 ◇ q25) ◇ (q25 ◇ q25))) (q25 ◇ (q26 ◇ (q25 ◇ q25)))))
  have apc27:=fun (q28:G)=>by
    exact (((cg (fun t => (q28 ◇ q28) ◇ t) (apc9 q28 q28 q28)).symm).trans (apc26 q28 (q28 ◇ q28) q28)).trans (cg (fun t => (q28 ◇ q28) ◇ t) (cg (fun t => t ◇ q28) (apc6 q28 q28 ((q28 ◇ q28) ◇ ((q28 ◇ q28) ◇ (q28 ◇ q28))) ((q28 ◇ q28) ◇ ((q28 ◇ q28) ◇ (q28 ◇ q28))) ((q28 ◇ q28) ◇ ((q28 ◇ q28) ◇ (q28 ◇ q28))) ((q28 ◇ q28) ◇ ((q28 ◇ q28) ◇ (q28 ◇ q28))))))
  have apc28:=fun (q29 q30 q31 q32:G)=>by
    exact ((cg (fun t => ((q30 ◇ q31) ◇ q32) ◇ t) (apc20 q29 q30 q31)).symm).trans (apc5 q32 (q31 ◇ (q30 ◇ q29)) (q30 ◇ q31))
  have apc31:=fun (q0 q1 q2 q4 q5 q6 q7:G)=>by
    exact ((cg (fun t => t ◇ (q0 ◇ (q4 ◇ (q1 ◇ q0)))) (cg (fun t => q4 ◇ t) (apc5 q0 q1 q0))).symm).trans ((apc3 q0 q1 q0 q4).trans (apc5 q0 q1 q0))
  have apc34:=fun (q33 q34 q35 q36:G)=>by
    exact (((cg (fun t => (q36 ◇ q35) ◇ t) (apc9 q36 q33 q34)).symm).trans (apc5 q35 (((q36 ◇ q36) ◇ (q33 ◇ q36)) ◇ q34) q36)).symm
  have apc35:=fun (q37 q38:G)=>by
    exact (((apc34 q37 q37 q38 q37).symm).trans (apc26 q37 (q37 ◇ q37) q38)).trans (cg (fun t => (q38 ◇ q38) ◇ t) (cg (fun t => t ◇ q38) (apc6 q37 q37 ((q37 ◇ q37) ◇ ((q37 ◇ q37) ◇ (q37 ◇ q37))) ((q37 ◇ q37) ◇ ((q37 ◇ q37) ◇ (q37 ◇ q37))) ((q37 ◇ q37) ◇ ((q37 ◇ q37) ◇ (q37 ◇ q37))) ((q37 ◇ q37) ◇ ((q37 ◇ q37) ◇ (q37 ◇ q37))))))
  have apc36:=fun (q39:G)=>by
    exact (((cg (fun t => t ◇ ((q39 ◇ q39) ◇ (q39 ◇ q39))) (apc27 q39)).symm).trans (apc20 ((q39 ◇ q39) ◇ q39) (q39 ◇ q39) (q39 ◇ q39))).trans (cg (fun t => t ◇ ((q39 ◇ q39) ◇ ((q39 ◇ q39) ◇ q39))) (apc6 q39 (q39 ◇ q39) (((q39 ◇ q39) ◇ q39) ◇ ((q39 ◇ q39) ◇ ((q39 ◇ q39) ◇ q39))) (((q39 ◇ q39) ◇ q39) ◇ ((q39 ◇ q39) ◇ ((q39 ◇ q39) ◇ q39))) (((q39 ◇ q39) ◇ q39) ◇ ((q39 ◇ q39) ◇ ((q39 ◇ q39) ◇ q39))) (((q39 ◇ q39) ◇ q39) ◇ ((q39 ◇ q39) ◇ ((q39 ◇ q39) ◇ q39)))))
  have apc37:=fun (q40:G)=>by
    exact ((cg (fun t => (q40 ◇ ((q40 ◇ q40) ◇ ((q40 ◇ q40) ◇ q40))) ◇ t) (apc6 q40 q40 ((q40 ◇ q40) ◇ ((q40 ◇ q40) ◇ (q40 ◇ q40))) ((q40 ◇ q40) ◇ ((q40 ◇ q40) ◇ (q40 ◇ q40))) ((q40 ◇ q40) ◇ ((q40 ◇ q40) ◇ (q40 ◇ q40))) ((q40 ◇ q40) ◇ ((q40 ◇ q40) ◇ (q40 ◇ q40))))).symm).trans ((((cg (fun t => t ◇ ((q40 ◇ q40) ◇ ((q40 ◇ q40) ◇ (q40 ◇ q40)))) (apc36 q40)).symm).trans (apc20 (q40 ◇ q40) (q40 ◇ q40) ((q40 ◇ q40) ◇ (q40 ◇ q40)))).trans (cg (fun t => t ◇ ((q40 ◇ q40) ◇ (q40 ◇ q40))) (apc6 q40 q40 ((q40 ◇ q40) ◇ ((q40 ◇ q40) ◇ (q40 ◇ q40))) ((q40 ◇ q40) ◇ ((q40 ◇ q40) ◇ (q40 ◇ q40))) ((q40 ◇ q40) ◇ ((q40 ◇ q40) ◇ (q40 ◇ q40))) ((q40 ◇ q40) ◇ ((q40 ◇ q40) ◇ (q40 ◇ q40))))))
  have apc41:=fun (q41 q42 q43:G)=>by
    exact ((cg (fun t => q42 ◇ t) (cg (fun t => t ◇ q42) (cg (fun t => t ◇ ((q41 ◇ q42) ◇ (q43 ◇ q41))) (apc5 q42 q43 q41)))).symm).trans (((cg (fun t => t ◇ ((((q41 ◇ q42) ◇ (q43 ◇ q41)) ◇ ((q41 ◇ q42) ◇ (q43 ◇ q41))) ◇ q42)) ((h q42 q43 q41).symm)).symm).trans (apc2 q42 q43 q41 ((q41 ◇ q42) ◇ (q43 ◇ q41))))
  have apc45:=fun (q44 q45 q46 q47:G)=>by
    exact ((cg (fun t => t ◇ ((q47 ◇ (q45 ◇ q46)) ◇ ((q46 ◇ q44) ◇ q47))) (apc5 q44 q45 q46)).symm).trans ((h (q45 ◇ q46) (q46 ◇ q44) q47).symm)
  have apc46:=fun (q44 q45 q46 q48:G)=>by
    exact ((cg (fun t => (q48 ◇ (q45 ◇ q46)) ◇ t) (cg (fun t => t ◇ (q48 ◇ (q46 ◇ q44))) (apc5 q44 q45 q46))).symm).trans ((h (q45 ◇ q46) q48 (q46 ◇ q44)).symm)
  have apc48:=fun (q49 q50 q51:G)=>by
    exact ((cg (fun t => ((q50 ◇ (q51 ◇ q49)) ◇ (q51 ◇ (q49 ◇ q50))) ◇ t) (apc45 q50 q51 q49 q50)).symm).trans (apc46 q50 q51 (q49 ◇ q50) (q50 ◇ (q51 ◇ q49)))
  have apc51:=fun (q52 q53 q54:G)=>by
    exact ((cg (fun t => t ◇ (q54 ◇ (q53 ◇ (q54 ◇ q52)))) (apc20 q52 q54 q53)).symm).trans (apc20 q53 q54 (q53 ◇ (q54 ◇ q52)))
  have apc52:=fun (q55 q56:G)=>by
    exact ((cg (fun t => t ◇ ((q55 ◇ q55) ◇ q55)) (cg (fun t => t ◇ ((q55 ◇ q55) ◇ (q56 ◇ q55))) (apc6 q55 q56 ((q56 ◇ q55) ◇ ((q55 ◇ q55) ◇ (q56 ◇ q55))) ((q56 ◇ q55) ◇ ((q55 ◇ q55) ◇ (q56 ◇ q55))) ((q56 ◇ q55) ◇ ((q55 ◇ q55) ◇ (q56 ◇ q55))) ((q56 ◇ q55) ◇ ((q55 ◇ q55) ◇ (q56 ◇ q55)))))).symm).trans ((((cg (fun t => (((q56 ◇ q55) ◇ ((q55 ◇ q55) ◇ (q56 ◇ q55))) ◇ ((q55 ◇ q55) ◇ (q56 ◇ q55))) ◇ t) (cg (fun t => (q55 ◇ q55) ◇ t) (apc6 q55 q56 q55 q55 q55 q55))).symm).trans (apc51 (q56 ◇ q55) (q56 ◇ q55) (q55 ◇ q55))).trans (cg (fun t => t ◇ ((q55 ◇ q55) ◇ (q56 ◇ q55))) (apc6 q55 q56 ((q56 ◇ q55) ◇ ((q55 ◇ q55) ◇ (q56 ◇ q55))) ((q56 ◇ q55) ◇ ((q55 ◇ q55) ◇ (q56 ◇ q55))) ((q56 ◇ q55) ◇ ((q55 ◇ q55) ◇ (q56 ◇ q55))) ((q56 ◇ q55) ◇ ((q55 ◇ q55) ◇ (q56 ◇ q55))))))
  have apc53:=fun (q57 q58:G)=>by
    exact ((apc5 q58 (((q57 ◇ q57) ◇ q57) ◇ q58) (q57 ◇ ((q57 ◇ q57) ◇ (q57 ◇ q57)))).symm).trans (((cg (fun t => ((q57 ◇ ((q57 ◇ q57) ◇ (q57 ◇ q57))) ◇ q58) ◇ t) (cg (fun t => (((q57 ◇ q57) ◇ q57) ◇ q58) ◇ t) (apc52 q57 q57))).symm).trans ((h q58 (q57 ◇ ((q57 ◇ q57) ◇ (q57 ◇ q57))) ((q57 ◇ q57) ◇ q57)).symm))
  have apc54:=fun (q59:G)=>by
    exact ((cg (fun t => q59 ◇ t) (cg (fun t => t ◇ q59) (cg (fun t => t ◇ q59) (apc53 q59 q59)))).symm).trans ((((cg (fun t => q59 ◇ t) (cg (fun t => t ◇ q59) (cg (fun t => ((q59 ◇ q59) ◇ ((((q59 ◇ q59) ◇ q59) ◇ q59) ◇ q59)) ◇ t) (apc53 q59 q59)))).symm).trans (apc41 q59 q59 (((q59 ◇ q59) ◇ q59) ◇ q59))).trans (apc53 q59 q59))
  have apc55:=fun (q60:G)=>by
    exact ((cg (fun t => t ◇ (q60 ◇ q60)) (cg (fun t => (q60 ◇ q60) ◇ t) (apc53 q60 q60))).symm).trans ((((cg (fun t => ((q60 ◇ q60) ◇ ((q60 ◇ q60) ◇ ((((q60 ◇ q60) ◇ q60) ◇ q60) ◇ q60))) ◇ t) (cg (fun t => q60 ◇ t) (apc53 q60 q60))).symm).trans (apc31 q60 (((q60 ◇ q60) ◇ q60) ◇ q60) q60 (q60 ◇ q60) q60 q60 q60)).trans (apc53 q60 q60))
  have apc56:=fun (q61:G)=>by
    exact (((cg (fun t => t ◇ ((q61 ◇ q61) ◇ q61)) (cg (fun t => q61 ◇ t) (apc53 q61 q61))).symm).trans (apc52 q61 (((q61 ◇ q61) ◇ q61) ◇ q61))).trans (cg (fun t => q61 ◇ t) (apc53 q61 q61))
  have apc57:=fun (q37 q38 q61:G)=>by
    exact (((cg (fun t => (q37 ◇ q38) ◇ t) (apc56 q37)).symm).trans (apc35 q37 q38)).symm
  have apc58:=fun (q62:G)=>by
    exact (((cg (fun t => t ◇ q62) (cg (fun t => (q62 ◇ q62) ◇ t) (cg (fun t => t ◇ q62) (apc54 q62)))).symm).trans (apc19 (q62 ◇ q62) q62)).trans ((cg (fun t => t ◇ ((q62 ◇ q62) ◇ q62)) (apc54 q62)).trans (apc54 q62))
  have apc59:=fun (q63:G)=>by
    exact (((cg (fun t => q63 ◇ t) (cg (fun t => q63 ◇ t) (cg (fun t => q63 ◇ t) (apc58 q63)))).symm).trans ((((cg (fun t => q63 ◇ t) (cg (fun t => q63 ◇ t) (cg (fun t => t ◇ (((q63 ◇ q63) ◇ (q63 ◇ q63)) ◇ q63)) (apc58 q63)))).symm).trans (apc8 q63 ((q63 ◇ q63) ◇ (q63 ◇ q63)) q63)).trans (cg (fun t => (q63 ◇ q63) ◇ t) (apc58 q63)))).symm
  have apc60:=fun (q64:G)=>by
    exact (((cg (fun t => q64 ◇ t) (apc54 q64)).symm).trans (((cg (fun t => t ◇ (q64 ◇ ((q64 ◇ q64) ◇ q64))) (apc55 q64)).symm).trans (apc20 q64 q64 ((q64 ◇ q64) ◇ q64)))).symm
  have apc61:=fun (q65:G)=>by
    exact ((cg (fun t => q65 ◇ t) (apc59 q65)).symm).trans (apc54 q65)
  have apc62:=fun (q66 q67:G)=>by
    exact ((cg (fun t => ((((q66 ◇ q66) ◇ q66) ◇ q67) ◇ q67) ◇ t) (apc53 q66 q67)).symm).trans ((h q67 (((q66 ◇ q66) ◇ q66) ◇ q67) q67).symm)
  have apc63:=fun (q68:G)=>by
    exact ((apc52 q68 q68).symm).trans (((cg (fun t => t ◇ ((q68 ◇ q68) ◇ q68)) (cg (fun t => t ◇ ((q68 ◇ q68) ◇ (q68 ◇ q68))) (apc54 q68))).symm).trans (apc48 q68 q68 (q68 ◇ q68)))
  have apc64:=fun (q40 q61:G)=>by
    exact (((cg (fun t => t ◇ q40) (cg (fun t => q40 ◇ t) (apc56 q40))).symm).trans (apc37 q40)).trans (apc63 q40)
  have apc65:=fun (q69 q70:G)=>by
    exact ((cg (fun t => (((q70 ◇ q70) ◇ q70) ◇ q69) ◇ t) (apc54 q70)).symm).trans (apc5 q69 q70 ((q70 ◇ q70) ◇ q70))
  have apc66:=fun (q71 q72:G)=>by
    exact (((cg (fun t => t ◇ ((q71 ◇ q71) ◇ q72)) (cg (fun t => q72 ◇ t) (apc56 q71))).symm).trans (apc20 ((q71 ◇ q71) ◇ q71) (q71 ◇ q71) q72)).trans (((cg (fun t => t ◇ ((q71 ◇ q71) ◇ ((q71 ◇ q71) ◇ q71))) (cg (fun t => ((q71 ◇ q71) ◇ q71) ◇ t) (apc56 q71))).trans (cg (fun t => t ◇ ((q71 ◇ q71) ◇ ((q71 ◇ q71) ◇ q71))) (apc55 q71))).trans (cg (fun t => q71 ◇ t) (apc56 q71)))
  have apc67:=fun (q73:G)=>by
    exact (((cg (fun t => t ◇ ((q73 ◇ q73) ◇ ((q73 ◇ q73) ◇ (q73 ◇ q73)))) (cg (fun t => (q73 ◇ q73) ◇ t) (apc6 q73 q73 ((q73 ◇ q73) ◇ ((q73 ◇ q73) ◇ (q73 ◇ q73))) ((q73 ◇ q73) ◇ ((q73 ◇ q73) ◇ (q73 ◇ q73))) ((q73 ◇ q73) ◇ ((q73 ◇ q73) ◇ (q73 ◇ q73))) ((q73 ◇ q73) ◇ ((q73 ◇ q73) ◇ (q73 ◇ q73)))))).trans (cg (fun t => ((q73 ◇ q73) ◇ q73) ◇ t) (apc6 q73 q73 ((q73 ◇ q73) ◇ ((q73 ◇ q73) ◇ (q73 ◇ q73))) ((q73 ◇ q73) ◇ ((q73 ◇ q73) ◇ (q73 ◇ q73))) ((q73 ◇ q73) ◇ ((q73 ◇ q73) ◇ (q73 ◇ q73))) ((q73 ◇ q73) ◇ ((q73 ◇ q73) ◇ (q73 ◇ q73)))))).symm).trans (((cg (fun t => t ◇ ((q73 ◇ q73) ◇ ((q73 ◇ q73) ◇ (q73 ◇ q73)))) (apc59 (q73 ◇ q73))).symm).trans (apc66 q73 ((q73 ◇ q73) ◇ (q73 ◇ q73))))
  have apc69:=fun (q74:G)=>by
    exact (((((cg (fun t => t ◇ ((q74 ◇ q74) ◇ (q74 ◇ q74))) (apc20 q74 q74 (q74 ◇ q74))).trans (cg (fun t => t ◇ ((q74 ◇ q74) ◇ (q74 ◇ q74))) (apc60 q74))).trans (apc6 q74 q74 ((q74 ◇ q74) ◇ ((q74 ◇ q74) ◇ (q74 ◇ q74))) ((q74 ◇ q74) ◇ ((q74 ◇ q74) ◇ (q74 ◇ q74))) ((q74 ◇ q74) ◇ ((q74 ◇ q74) ◇ (q74 ◇ q74))) ((q74 ◇ q74) ◇ ((q74 ◇ q74) ◇ (q74 ◇ q74))))).symm).trans ((((cg (fun t => t ◇ ((q74 ◇ q74) ◇ (q74 ◇ q74))) (cg (fun t => ((q74 ◇ q74) ◇ (q74 ◇ q74)) ◇ t) (apc66 q74 (q74 ◇ q74)))).symm).trans (apc64 ((q74 ◇ q74) ◇ (q74 ◇ q74)) q74)).trans ((cg (fun t => t ◇ (((q74 ◇ q74) ◇ (q74 ◇ q74)) ◇ ((q74 ◇ q74) ◇ (q74 ◇ q74)))) (apc66 q74 (q74 ◇ q74))).trans (cg (fun t => (q74 ◇ (q74 ◇ q74)) ◇ t) (apc66 q74 (q74 ◇ q74)))))).symm
  have apc73:=fun (q75 q76:G)=>by
    exact (((cg (fun t => ((q75 ◇ q75) ◇ q76) ◇ t) (apc55 q75)).symm).trans (apc5 q76 ((q75 ◇ q75) ◇ q75) (q75 ◇ q75))).symm
  have apc78:=fun (q77 q78 q79:G)=>by
    exact ((cg (fun t => (((q77 ◇ q77) ◇ q78) ◇ q79) ◇ t) (apc56 q77)).symm).trans (apc10 q77 (q77 ◇ q77) q78 q79)
  have apc80:=fun (q80 q81:G)=>by
    exact ((cg (fun t => t ◇ (q81 ◇ ((q80 ◇ q80) ◇ (q80 ◇ q80)))) (apc58 q80)).symm).trans (apc5 q80 q81 ((q80 ◇ q80) ◇ (q80 ◇ q80)))
  have apc84:=fun (q82 q83 q84:G)=>by
    exact (((cg (fun t => ((q82 ◇ q83) ◇ q84) ◇ t) (apc60 q82)).symm).trans (apc28 q82 q82 q83 q84)).symm
  have apc88:=fun (q85 q86 q87:G)=>by
    exact ((cg (fun t => (((q85 ◇ (q85 ◇ q85)) ◇ q86) ◇ q87) ◇ t) (apc6 q85 q85 ((q85 ◇ q85) ◇ ((q85 ◇ q85) ◇ (q85 ◇ q85))) ((q85 ◇ q85) ◇ ((q85 ◇ q85) ◇ (q85 ◇ q85))) ((q85 ◇ q85) ◇ ((q85 ◇ q85) ◇ (q85 ◇ q85))) ((q85 ◇ q85) ◇ ((q85 ◇ q85) ◇ (q85 ◇ q85))))).symm).trans (((cg (fun t => (((q85 ◇ (q85 ◇ q85)) ◇ q86) ◇ q87) ◇ t) (cg (fun t => (q85 ◇ q85) ◇ t) (apc64 q85 q85))).symm).trans (apc10 q85 (q85 ◇ (q85 ◇ q85)) q86 q87))
  have apc89:=fun (q88 q89:G)=>by
    exact ((((cg (fun t => t ◇ q88) (cg (fun t => t ◇ q89) (apc69 q88))).symm).trans (apc88 q88 (q88 ◇ (q88 ◇ q88)) q89)).trans ((cg (fun t => (q89 ◇ q89) ◇ t) (cg (fun t => t ◇ q89) (apc64 q88 ((q88 ◇ (q88 ◇ q88)) ◇ q88)))).trans (apc84 q88 (q88 ◇ q88) q89))).symm
  have apc96:=fun (q90 q91:G)=>by
    exact ((cg (fun t => (q91 ◇ q90) ◇ t) (apc59 q91)).symm).trans (apc5 q90 (q91 ◇ q91) q91)
  have apc97:=fun (q92 q93:G)=>by
    exact ((cg (fun t => ((q92 ◇ q92) ◇ q93) ◇ t) (cg (fun t => (q92 ◇ q92) ◇ t) (apc6 q92 q92 ((q92 ◇ q92) ◇ ((q92 ◇ q92) ◇ (q92 ◇ q92))) ((q92 ◇ q92) ◇ ((q92 ◇ q92) ◇ (q92 ◇ q92))) ((q92 ◇ q92) ◇ ((q92 ◇ q92) ◇ (q92 ◇ q92))) ((q92 ◇ q92) ◇ ((q92 ◇ q92) ◇ (q92 ◇ q92)))))).symm).trans ((((cg (fun t => ((q92 ◇ q92) ◇ q93) ◇ t) (cg (fun t => (q92 ◇ q92) ◇ t) (cg (fun t => (q92 ◇ q92) ◇ t) (apc5 q92 q92 q92)))).symm).trans (apc96 q93 (q92 ◇ q92))).trans ((apc84 q92 (q92 ◇ q92) q93).trans (apc89 q92 q93)))
  have apc99:=fun (q94 q95:G)=>by
    exact (((cg (fun t => t ◇ (q95 ◇ (q94 ◇ (q94 ◇ q94)))) (apc69 q94)).symm).trans (apc57 q95 (q94 ◇ (q94 ◇ q94)) q94)).symm
  have apc100:=fun (q96 q97:G)=>by
    exact ((cg (fun t => (q96 ◇ (q96 ◇ q96)) ◇ t) (cg (fun t => q97 ◇ t) (cg (fun t => q96 ◇ t) (apc69 q96)))).symm).trans ((((cg (fun t => (q96 ◇ (q96 ◇ q96)) ◇ t) (cg (fun t => q97 ◇ t) (cg (fun t => t ◇ ((q96 ◇ (q96 ◇ q96)) ◇ (q96 ◇ (q96 ◇ q96)))) (apc69 q96)))).symm).trans (apc80 (q96 ◇ (q96 ◇ q96)) q97)).trans (cg (fun t => t ◇ (q97 ◇ (q96 ◇ (q96 ◇ q96)))) (apc69 q96)))
  have apc106:=fun (q98 q99 q100:G)=>by
    exact ((cg (fun t => q100 ◇ t) (apc10 q100 q100 q98 q99)).symm).trans (apc80 q100 ((q100 ◇ q98) ◇ q99))
  have apc107:=fun (q101 q102:G)=>by
    exact (((((cg (fun t => (q101 ◇ q102) ◇ t) (cg (fun t => (q102 ◇ q102) ◇ t) (cg (fun t => t ◇ q102) (apc5 q101 q101 q102)))).trans (cg (fun t => (q101 ◇ q102) ◇ t) (apc84 q101 (q101 ◇ q101) q102))).trans (cg (fun t => (q101 ◇ q102) ◇ t) (apc89 q101 q102))).symm).trans ((((cg (fun t => (q101 ◇ q102) ◇ t) (apc106 q101 (q101 ◇ q102) q102)).symm).trans (apc80 (q101 ◇ q102) q102)).trans (apc57 q102 (q101 ◇ q102) (((q101 ◇ q102) ◇ (q101 ◇ q102)) ◇ (q102 ◇ (q101 ◇ q102)))))).symm
  have apc108:=fun (q103 q104:G)=>by
    exact (((((((cg (fun t => t ◇ (q103 ◇ ((q103 ◇ (q103 ◇ q103)) ◇ (q103 ◇ (q103 ◇ q103))))) (cg (fun t => ((q103 ◇ (q103 ◇ q103)) ◇ (q103 ◇ (q103 ◇ q103))) ◇ t) (cg (fun t => q104 ◇ t) (apc100 q103 q103)))).trans (cg (fun t => t ◇ (q103 ◇ ((q103 ◇ (q103 ◇ q103)) ◇ (q103 ◇ (q103 ◇ q103))))) (cg (fun t => ((q103 ◇ (q103 ◇ q103)) ◇ (q103 ◇ (q103 ◇ q103))) ◇ t) (cg (fun t => q104 ◇ t) (apc61 q103))))).trans (cg (fun t => t ◇ (q103 ◇ ((q103 ◇ (q103 ◇ q103)) ◇ (q103 ◇ (q103 ◇ q103))))) (cg (fun t => t ◇ (q104 ◇ q103)) (apc100 q103 q103)))).trans (cg (fun t => t ◇ (q103 ◇ ((q103 ◇ (q103 ◇ q103)) ◇ (q103 ◇ (q103 ◇ q103))))) (cg (fun t => t ◇ (q104 ◇ q103)) (apc61 q103)))).trans (cg (fun t => (q103 ◇ (q104 ◇ q103)) ◇ t) (cg (fun t => q103 ◇ t) (apc100 q103 q103)))).trans (cg (fun t => (q103 ◇ (q104 ◇ q103)) ◇ t) (cg (fun t => q103 ◇ t) (apc61 q103)))).symm).trans ((((cg (fun t => (((q103 ◇ (q103 ◇ q103)) ◇ (q103 ◇ (q103 ◇ q103))) ◇ (q104 ◇ ((q103 ◇ (q103 ◇ q103)) ◇ (q103 ◇ (q103 ◇ q103))))) ◇ t) (apc99 q103 (q103 ◇ (q103 ◇ q103)))).symm).trans (apc107 q104 ((q103 ◇ (q103 ◇ q103)) ◇ (q103 ◇ (q103 ◇ q103))))).trans (((((cg (fun t => (q104 ◇ ((q103 ◇ (q103 ◇ q103)) ◇ (q103 ◇ (q103 ◇ q103)))) ◇ t) (cg (fun t => t ◇ q104) (cg (fun t => q104 ◇ t) (apc100 q103 q103)))).trans (cg (fun t => (q104 ◇ ((q103 ◇ (q103 ◇ q103)) ◇ (q103 ◇ (q103 ◇ q103)))) ◇ t) (cg (fun t => t ◇ q104) (cg (fun t => q104 ◇ t) (apc61 q103))))).trans (cg (fun t => t ◇ ((q104 ◇ q103) ◇ q104)) (cg (fun t => q104 ◇ t) (apc100 q103 q103)))).trans (cg (fun t => t ◇ ((q104 ◇ q103) ◇ q104)) (cg (fun t => q104 ◇ t) (apc61 q103)))).trans (apc5 q103 (q104 ◇ q103) q104)))
  have apc116:=fun (q105 q106:G)=>by
    exact (((cg (fun t => (((q105 ◇ q105) ◇ q105) ◇ q106) ◇ t) (apc53 q105 ((q105 ◇ q105) ◇ q105))).symm).trans (apc35 ((q105 ◇ q105) ◇ q105) q106)).trans (apc73 q105 q106)
  have apc117:=fun (q107 q108:G)=>by
    exact (((cg (fun t => t ◇ q108) (apc56 q108)).symm).trans ((((cg (fun t => ((q108 ◇ q108) ◇ ((q108 ◇ q108) ◇ q108)) ◇ t) (apc53 q107 q108)).symm).trans (apc21 q108 (((q107 ◇ q107) ◇ q107) ◇ q108) (q108 ◇ q108))).trans ((cg (fun t => t ◇ ((q108 ◇ q108) ◇ (((q107 ◇ q107) ◇ q107) ◇ q108))) (cg (fun t => (((q107 ◇ q107) ◇ q107) ◇ q108) ◇ t) (apc73 q107 q108))).trans (cg (fun t => ((((q107 ◇ q107) ◇ q107) ◇ q108) ◇ (((q107 ◇ q107) ◇ q108) ◇ q107)) ◇ t) (apc73 q107 q108))))).symm
  have apc119:=fun (q109 q110:G)=>by
    exact ((cg (fun t => (((q109 ◇ q109) ◇ q109) ◇ q110) ◇ t) (cg (fun t => ((q109 ◇ q109) ◇ q110) ◇ t) (apc55 q109))).symm).trans ((h q110 ((q109 ◇ q109) ◇ q109) (q109 ◇ q109)).symm)
  have apc120:=fun (q107 q108 q109 q110:G)=>by
    exact ((cg (fun t => t ◇ (((q107 ◇ q107) ◇ q108) ◇ q107)) (apc119 q107 q108)).symm).trans (apc117 q107 q108)
  have apc122:=fun (q111 q112:G)=>by
    exact ((((((((((cg (fun t => t ◇ (((q111 ◇ q111) ◇ ((q112 ◇ q112) ◇ q112)) ◇ q111)) (cg (fun t => t ◇ (((q111 ◇ q111) ◇ ((q112 ◇ q112) ◇ q112)) ◇ q111)) (cg (fun t => t ◇ ((q112 ◇ q112) ◇ q112)) (apc97 q112 q112)))).trans (cg (fun t => t ◇ (((q111 ◇ q111) ◇ ((q112 ◇ q112) ◇ q112)) ◇ q111)) (cg (fun t => t ◇ (((q111 ◇ q111) ◇ ((q112 ◇ q112) ◇ q112)) ◇ q111)) (apc97 q112 q112)))).trans (cg (fun t => t ◇ (((q111 ◇ q111) ◇ ((q112 ◇ q112) ◇ q112)) ◇ q111)) (apc120 q111 ((q112 ◇ q112) ◇ q112) (((q112 ◇ q112) ◇ q112) ◇ (((q111 ◇ q111) ◇ ((q112 ◇ q112) ◇ q112)) ◇ q111)) (((q112 ◇ q112) ◇ q112) ◇ (((q111 ◇ q111) ◇ ((q112 ◇ q112) ◇ q112)) ◇ q111))))).trans (cg (fun t => t ◇ (((q111 ◇ q111) ◇ ((q112 ◇ q112) ◇ q112)) ◇ q111)) (cg (fun t => t ◇ ((q112 ◇ q112) ◇ q112)) (apc97 q112 q112)))).trans (cg (fun t => t ◇ (((q111 ◇ q111) ◇ ((q112 ◇ q112) ◇ q112)) ◇ q111)) (apc97 q112 q112))).trans (apc120 q111 ((q112 ◇ q112) ◇ q112) (((q112 ◇ q112) ◇ q112) ◇ (((q111 ◇ q111) ◇ ((q112 ◇ q112) ◇ q112)) ◇ q111)) (((q112 ◇ q112) ◇ q112) ◇ (((q111 ◇ q111) ◇ ((q112 ◇ q112) ◇ q112)) ◇ q111)))).trans (cg (fun t => t ◇ ((q112 ◇ q112) ◇ q112)) (apc97 q112 q112))).trans (apc97 q112 q112)).symm).trans (((cg (fun t => t ◇ (((q111 ◇ q111) ◇ ((q112 ◇ q112) ◇ q112)) ◇ q111)) (cg (fun t => t ◇ (((q111 ◇ q111) ◇ ((q112 ◇ q112) ◇ q112)) ◇ q111)) (apc120 q111 ((q112 ◇ q112) ◇ q112) q111 q111))).symm).trans (apc62 q112 (((q111 ◇ q111) ◇ ((q112 ◇ q112) ◇ q112)) ◇ q111)))).symm
  have apc123:=fun (q113 q114:G)=>by
    exact (((cg (fun t => t ◇ (q114 ◇ q114)) (apc122 q114 q113)).symm).trans (apc78 q114 ((q113 ◇ q113) ◇ q113) q114)).trans (apc53 q113 q114)
  have apc124:=fun (q115 q116:G)=>by
    exact (((apc58 q116).symm).trans ((((cg (fun t => ((q116 ◇ q116) ◇ (q116 ◇ q116)) ◇ t) (apc123 q115 q116)).symm).trans (apc57 ((q115 ◇ q115) ◇ q115) (q116 ◇ q116) q115)).trans ((cg (fun t => t ◇ (((q115 ◇ q115) ◇ q115) ◇ ((q115 ◇ q115) ◇ q115))) (apc123 q115 q116)).trans (cg (fun t => q116 ◇ t) (apc97 q115 q115))))).symm
  have apc126:=fun (q115 q116 q92 q93:G)=>by
    exact (((apc124 q92 ((q92 ◇ q92) ◇ q93)).symm).trans (apc97 q92 q93)).symm
  have apc127:=fun (q117 q118:G)=>by
    exact (((cg (fun t => t ◇ ((q117 ◇ q117) ◇ q118)) (apc124 q117 q118)).symm).trans (apc20 q117 (q117 ◇ q117) q118)).trans ((cg (fun t => t ◇ ((q117 ◇ q117) ◇ q117)) (apc124 q117 q117)).trans (apc124 q117 q117))
  have apc128:=fun (q119 q120:G)=>by
    exact ((cg (fun t => q120 ◇ t) (cg (fun t => t ◇ q120) (apc61 q119))).symm).trans (((cg (fun t => q120 ◇ t) (cg (fun t => t ◇ q120) (apc100 q119 q119))).symm).trans (apc127 (q119 ◇ (q119 ◇ q119)) q120))
  have apc129:=fun (q121 q122:G)=>by
    exact (((apc5 q122 ((q121 ◇ q121) ◇ q121) q121).trans (apc73 q121 q122)).symm).trans ((((cg (fun t => t ◇ (((q121 ◇ q121) ◇ q121) ◇ q121)) (cg (fun t => q121 ◇ t) (apc123 q121 q122))).symm).trans (apc20 (q122 ◇ q122) ((q121 ◇ q121) ◇ q121) q121)).trans (((cg (fun t => t ◇ (((q121 ◇ q121) ◇ q121) ◇ (q122 ◇ q122))) (cg (fun t => (q122 ◇ q122) ◇ t) (apc123 q121 q122))).trans (cg (fun t => ((q122 ◇ q122) ◇ q122) ◇ t) (apc123 q121 q122))).trans (apc67 q122)))
  have apc132:=fun (q123 q124:G)=>by
    exact (((apc58 q123).symm).trans (((cg (fun t => ((q123 ◇ q123) ◇ (q123 ◇ q123)) ◇ t) (apc123 q124 q123)).symm).trans (apc73 q124 (q123 ◇ q123)))).symm
  have apc133:=fun (q125 q126:G)=>by
    exact ((cg (fun t => q126 ◇ t) (cg (fun t => q126 ◇ t) (cg (fun t => q125 ◇ t) (apc132 q125 q126)))).symm).trans ((((cg (fun t => q126 ◇ t) (cg (fun t => q126 ◇ t) (cg (fun t => t ◇ (((q126 ◇ q126) ◇ (q125 ◇ q125)) ◇ q126)) (apc132 q125 q126)))).symm).trans (apc8 q126 ((q126 ◇ q126) ◇ (q125 ◇ q125)) q125)).trans (cg (fun t => (q126 ◇ q126) ◇ t) (apc132 q125 q126)))
  have apc134:=fun (q127 q128:G)=>by
    exact (((apc5 q127 q128 q128).symm).trans ((((cg (fun t => t ◇ (q128 ◇ q128)) (cg (fun t => q128 ◇ t) (apc132 q127 q128))).symm).trans (apc108 q128 ((q128 ◇ q128) ◇ (q127 ◇ q127)))).trans ((cg (fun t => (q128 ◇ q128) ◇ t) (cg (fun t => t ◇ q128) (apc132 q127 q128))).trans (apc57 q127 q128 ((q128 ◇ q128) ◇ (q127 ◇ q128)))))).symm
  have apc135:=fun (q129 q130:G)=>by
    exact (((cg (fun t => t ◇ q130) (apc123 q130 q129)).symm).trans (apc65 (q129 ◇ q129) q130)).symm
  have apc136:=fun (q131 q132:G)=>by
    exact ((cg (fun t => ((q132 ◇ q132) ◇ q131) ◇ t) (apc124 q132 (q132 ◇ q131))).symm).trans ((h q131 (q132 ◇ q132) q132).symm)
  have apc137:=fun (q127 q128 q37 q38 q61:G)=>by
    exact (apc57 q37 q38 q37).trans (apc134 q37 q38)
  have apc139:=fun (q133 q134:G)=>by
    exact (((apc124 q134 (q134 ◇ q133)).symm).trans (apc5 q133 (q134 ◇ q134) q134)).symm
  have apc140:=fun (q135 q136:G)=>by
    exact ((((apc139 (q136 ◇ q136) q135).symm).trans ((apc12 q136 q136 q136 (q135 ◇ q135)).symm)).trans ((apc137 (((q136 ◇ q136) ◇ (q136 ◇ q136)) ◇ ((q135 ◇ q135) ◇ (q136 ◇ q136))) (((q136 ◇ q136) ◇ (q136 ◇ q136)) ◇ ((q135 ◇ q135) ◇ (q136 ◇ q136))) (q135 ◇ q135) (q136 ◇ q136) (((q136 ◇ q136) ◇ (q136 ◇ q136)) ◇ ((q135 ◇ q135) ◇ (q136 ◇ q136)))).trans (apc139 (q135 ◇ q135) q136))).symm
  have apc142:=fun (q137 q138:G)=>by
    exact (((((cg (fun t => t ◇ (q138 ◇ q138)) (cg (fun t => q138 ◇ t) (apc20 q137 q137 (q137 ◇ q137)))).trans (cg (fun t => t ◇ (q138 ◇ q138)) (cg (fun t => q138 ◇ t) (apc60 q137)))).trans (cg (fun t => t ◇ (q138 ◇ q138)) (apc140 q137 q138))).symm).trans ((((cg (fun t => t ◇ (q138 ◇ q138)) (cg (fun t => q138 ◇ t) (cg (fun t => ((q137 ◇ q137) ◇ (q137 ◇ q137)) ◇ t) (apc135 q137 (q137 ◇ q137))))).symm).trans (apc99 ((q137 ◇ q137) ◇ (q137 ◇ q137)) q138)).trans ((((cg (fun t => ((q137 ◇ q137) ◇ (q137 ◇ q137)) ◇ t) (cg (fun t => q138 ◇ t) (cg (fun t => ((q137 ◇ q137) ◇ (q137 ◇ q137)) ◇ t) (apc139 (q137 ◇ q137) q137)))).trans (cg (fun t => ((q137 ◇ q137) ◇ (q137 ◇ q137)) ◇ t) (cg (fun t => q138 ◇ t) (apc20 q137 q137 (q137 ◇ q137))))).trans (cg (fun t => ((q137 ◇ q137) ◇ (q137 ◇ q137)) ◇ t) (cg (fun t => q138 ◇ t) (apc60 q137)))).trans (cg (fun t => ((q137 ◇ q137) ◇ (q137 ◇ q137)) ◇ t) (apc140 q137 q138))))).symm
  have apc145:=fun (q139 q140:G)=>by
    exact (((apc127 q139 (q140 ◇ q139)).symm).trans (((cg (fun t => (q140 ◇ q139) ◇ t) (apc5 q139 q140 q140)).symm).trans (apc133 q140 (q140 ◇ q139)))).symm
  have apc146:=fun (q141 q142 q143:G)=>by
    exact (((cg (fun t => (q143 ◇ q142) ◇ t) (apc145 q141 q143)).symm).trans (apc5 q142 ((q143 ◇ q141) ◇ (q143 ◇ q141)) q143)).trans (apc139 q142 (q143 ◇ q141))
  have apc147:=fun (q144 q145:G)=>by
    exact ((cg (fun t => t ◇ ((q145 ◇ q144) ◇ q145)) (apc145 q144 q145)).symm).trans (apc136 q145 (q145 ◇ q144))
  have apc148:=fun (q146 q147:G)=>by
    exact (((apc146 q147 (q147 ◇ q147) q146).symm).trans (((cg (fun t => t ◇ q147) (apc140 q146 q147)).symm).trans (apc126 q146 q146 q147 (q146 ◇ q146)))).symm
  have apc151:=fun (q148 q149:G)=>by
    exact (((apc124 q149 q148).symm).trans ((((cg (fun t => t ◇ ((q149 ◇ q149) ◇ q149)) (apc123 q149 q148)).symm).trans (apc116 q149 (q148 ◇ q148))).trans (cg (fun t => t ◇ q149) (apc148 q148 q149)))).symm
  have apc153:=fun (q150 q151:G)=>by
    exact (((apc146 q151 (q151 ◇ q151) q150).symm).trans (((cg (fun t => t ◇ q151) (cg (fun t => t ◇ (q151 ◇ q151)) (apc145 q150 q151))).symm).trans (apc151 ((q151 ◇ q150) ◇ (q151 ◇ q150)) q151))).symm
  have apc157:=fun (q152 q153:G)=>by
    exact ((((cg (fun t => t ◇ (q153 ◇ q152)) (cg (fun t => q152 ◇ t) (cg (fun t => q153 ◇ t) (cg (fun t => q152 ◇ t) (apc146 q152 q153 q153))))).trans (cg (fun t => t ◇ (q153 ◇ q152)) (cg (fun t => q152 ◇ t) (cg (fun t => q153 ◇ t) (apc147 q152 q153))))).trans (apc146 (q153 ◇ q152) (q153 ◇ q153) q152)).symm).trans ((((cg (fun t => t ◇ (q153 ◇ q152)) (cg (fun t => t ◇ (q153 ◇ (q152 ◇ ((q153 ◇ q153) ◇ q152)))) (apc136 q152 q153))).symm).trans (apc48 q152 ((q153 ◇ q153) ◇ q152) q153)).trans ((cg (fun t => q153 ◇ t) (cg (fun t => q152 ◇ t) (apc146 q152 q153 q153))).trans (cg (fun t => q153 ◇ t) (apc147 q152 q153))))
  have apc159:=fun (q154 q155 q156:G)=>by
    exact ((cg (fun t => q154 ◇ t) (apc153 q155 q156)).symm).trans ((((apc140 q154 (q156 ◇ q155)).symm).trans (apc146 (q154 ◇ q154) q155 q156)).trans ((cg (fun t => t ◇ q155) (apc140 q154 q156)).trans (apc146 q155 (q156 ◇ q156) q154)))
  have apc162:=fun (q157 q158:G)=>by
    exact (((cg (fun t => q157 ◇ t) (apc124 q157 q158)).symm).trans ((((cg (fun t => t ◇ (q158 ◇ ((q157 ◇ q157) ◇ q157))) (apc123 q157 q157)).symm).trans (apc5 (q157 ◇ q157) q158 ((q157 ◇ q157) ◇ q157))).trans ((cg (fun t => ((q157 ◇ q157) ◇ (q157 ◇ q157)) ◇ t) (apc140 q157 q158)).trans (apc142 q157 q158)))).symm
  have apc164:=fun (q159 q160 q161:G)=>by
    exact (((((((((cg (fun t => t ◇ ((q160 ◇ q159) ◇ (q160 ◇ q159))) (cg (fun t => q161 ◇ t) (apc146 q159 (q160 ◇ q159) q160))).trans (cg (fun t => t ◇ ((q160 ◇ q159) ◇ (q160 ◇ q159))) (cg (fun t => q161 ◇ t) (apc153 q159 q160)))).trans (cg (fun t => (q161 ◇ ((q159 ◇ q160) ◇ (q160 ◇ q160))) ◇ t) (apc153 q159 q160))).trans (cg (fun t => t ◇ ((q159 ◇ q160) ◇ (q160 ◇ q160))) (apc159 q161 q159 q160))).trans (apc159 ((q161 ◇ q159) ◇ (q160 ◇ q160)) q159 q160)).trans (apc146 (q160 ◇ q160) q159 ((q161 ◇ q159) ◇ (q160 ◇ q160)))).trans (cg (fun t => t ◇ q159) (apc162 (q161 ◇ q159) q160))).trans (apc146 q159 q160 (q161 ◇ q159))).symm).trans (((cg (fun t => t ◇ ((q160 ◇ q159) ◇ (q160 ◇ q159))) (cg (fun t => q161 ◇ t) (apc146 (q160 ◇ q159) q159 q160))).symm).trans (apc162 q161 (q160 ◇ q159)))
  have apc167:=fun (q162 q163 q164:G)=>by
    exact ((((apc124 q162 ((q164 ◇ q163) ◇ q163)).symm).trans (apc164 q163 ((q162 ◇ q162) ◇ q162) q164)).trans (cg (fun t => q164 ◇ t) (apc164 q162 q163 q162))).symm
  have apc168:=fun (q165 q166 q167:G)=>by
    exact ((((apc164 q167 q166 q165).symm).trans (apc146 q166 q167 (q165 ◇ q167))).trans (cg (fun t => t ◇ q167) (apc146 q166 q167 q165))).symm
  have apc169:=fun (q168 q169 q170:G)=>by
    exact ((((cg (fun t => t ◇ q169) (apc162 q170 q168)).symm).trans (apc164 (q168 ◇ q168) q169 q170)).trans (cg (fun t => q170 ◇ t) (apc140 q168 q169))).symm
  have apc170:=fun (q171 q172:G)=>by
    exact ((cg (fun t => t ◇ ((q171 ◇ q171) ◇ (q171 ◇ q172))) (apc124 q171 q172)).symm).trans (((apc124 q171 ((q172 ◇ ((q171 ◇ q171) ◇ q171)) ◇ ((q171 ◇ q171) ◇ (q171 ◇ q172)))).symm).trans (apc48 q171 q172 (q171 ◇ q171)))
  have apc173:=fun (q173 q174:G)=>by
    exact ((apc146 (q173 ◇ q174) q174 (q173 ◇ q173)).symm).trans (((cg (fun t => ((q173 ◇ q173) ◇ q174) ◇ t) (cg (fun t => t ◇ q174) (apc127 q173 q174))).symm).trans (apc147 ((q173 ◇ q173) ◇ q174) q174))
  have apc177:=fun (q175 q165 q166 q167:G)=>by
    exact (((apc146 q166 (q167 ◇ q175) q165).symm).trans ((((cg (fun t => t ◇ q166) (apc164 q175 q167 q165)).symm).trans (apc146 q166 q167 ((q165 ◇ q175) ◇ q175))).trans ((cg (fun t => t ◇ q167) (apc164 q175 q166 q165)).trans (apc146 q167 (q166 ◇ q175) q165)))).symm
  have apc179:=fun (q176 q177 q178:G)=>by
    exact ((apc146 (q177 ◇ q177) q178 (q177 ◇ q177)).symm).trans ((((cg (fun t => t ◇ (q177 ◇ q177)) (apc124 q176 ((q177 ◇ q177) ◇ q178))).symm).trans (apc78 q177 q178 ((q176 ◇ q176) ◇ q176))).trans (((cg (fun t => (((q176 ◇ q176) ◇ q176) ◇ ((q176 ◇ q176) ◇ q176)) ◇ t) (apc124 q176 (q178 ◇ q177))).trans (cg (fun t => t ◇ (q178 ◇ q177)) (apc124 q176 ((q176 ◇ q176) ◇ q176)))).trans (apc146 (q178 ◇ q177) q176 (q176 ◇ q176))))
  have apc180:=fun (q179 q180:G)=>by
    exact ((((cg (fun t => t ◇ q180) (apc169 q179 q180 (q179 ◇ q179))).trans (cg (fun t => t ◇ q180) (apc164 q179 q180 q179))).trans (apc146 q180 (q180 ◇ q179) q179)).symm).trans ((((cg (fun t => t ◇ q180) (apc170 q179 (q180 ◇ q180))).symm).trans ((apc179 q180 (q179 ◇ (q180 ◇ q180)) (q179 ◇ q179)).symm)).trans (((((((((((((cg (fun t => t ◇ (q179 ◇ q179)) (cg (fun t => t ◇ ((q179 ◇ (q180 ◇ q180)) ◇ (q179 ◇ (q180 ◇ q180)))) (apc169 q179 q180 (q179 ◇ (q180 ◇ q180))))).trans (cg (fun t => t ◇ (q179 ◇ q179)) (cg (fun t => t ◇ ((q179 ◇ (q180 ◇ q180)) ◇ (q179 ◇ (q180 ◇ q180)))) (cg (fun t => t ◇ q180) (apc146 q179 (q180 ◇ q180) q179))))).trans (cg (fun t => t ◇ (q179 ◇ q179)) (cg (fun t => (((q179 ◇ q179) ◇ (q180 ◇ q180)) ◇ q180) ◇ t) (apc169 q179 q180 (q179 ◇ (q180 ◇ q180)))))).trans (cg (fun t => t ◇ (q179 ◇ q179)) (cg (fun t => (((q179 ◇ q179) ◇ (q180 ◇ q180)) ◇ q180) ◇ t) (cg (fun t => t ◇ q180) (apc146 q179 (q180 ◇ q180) q179))))).trans (cg (fun t => t ◇ (q179 ◇ q179)) (apc177 q180 ((q179 ◇ q179) ◇ (q180 ◇ q180)) ((q179 ◇ q179) ◇ (q180 ◇ q180)) q180))).trans (cg (fun t => t ◇ (q179 ◇ q179)) (cg (fun t => t ◇ (q180 ◇ q180)) (apc169 (q179 ◇ q179) q180 ((q179 ◇ q179) ◇ (q180 ◇ q180)))))).trans (cg (fun t => t ◇ (q179 ◇ q179)) (cg (fun t => t ◇ (q180 ◇ q180)) (cg (fun t => t ◇ q180) (apc146 (q179 ◇ q179) (q180 ◇ q180) (q179 ◇ q179)))))).trans (cg (fun t => t ◇ (q179 ◇ q179)) (apc146 (q180 ◇ q180) q180 (((q179 ◇ q179) ◇ (q179 ◇ q179)) ◇ (q180 ◇ q180))))).trans (cg (fun t => t ◇ (q179 ◇ q179)) (cg (fun t => t ◇ q180) (apc162 ((q179 ◇ q179) ◇ (q179 ◇ q179)) q180)))).trans (cg (fun t => t ◇ (q179 ◇ q179)) (apc168 (q179 ◇ q179) (q179 ◇ q179) q180))).trans (cg (fun t => t ◇ (q179 ◇ q179)) (apc177 q180 q179 (q179 ◇ q179) q179))).trans (apc146 (q179 ◇ q179) (q179 ◇ q180) (q179 ◇ (q179 ◇ q179)))).trans (cg (fun t => t ◇ (q179 ◇ q180)) (apc157 q179 q179))))
  have apc187:=fun (q181 q182:G)=>by
    exact (((((cg (fun t => t ◇ (q182 ◇ q182)) (apc167 q181 q181 q182)).trans (apc146 (q182 ◇ q182) q181 (q182 ◇ q181))).trans (cg (fun t => t ◇ q181) (apc5 q181 q182 q182))).symm).trans ((((cg (fun t => t ◇ (q182 ◇ q182)) (cg (fun t => q182 ◇ t) (apc129 q182 q181))).symm).trans (apc108 q182 ((q182 ◇ q182) ◇ q181))).trans (((((((cg (fun t => (q182 ◇ q182) ◇ t) (cg (fun t => t ◇ q182) (cg (fun t => t ◇ q182) (apc146 q181 q182 q182)))).trans (cg (fun t => (q182 ◇ q182) ◇ t) (cg (fun t => t ◇ q182) (apc168 q182 q181 q182)))).trans (cg (fun t => (q182 ◇ q182) ◇ t) (cg (fun t => t ◇ q182) (apc128 q181 q182)))).trans (cg (fun t => (q182 ◇ q182) ◇ t) (apc146 q182 (q181 ◇ q181) q181))).trans (cg (fun t => (q182 ◇ q182) ◇ t) (apc177 q181 q181 q181 q182))).trans (apc177 (q182 ◇ q181) q182 (q181 ◇ q181) q182)).trans (cg (fun t => t ◇ (q182 ◇ (q182 ◇ q181))) (apc140 q181 q182))))).symm
  have apc188:=fun (q183 q184:G)=>by
    exact ((((((((((((((cg (fun t => ((q184 ◇ ((q184 ◇ q183) ◇ q184)) ◇ ((q184 ◇ q183) ◇ q184)) ◇ t) (cg (fun t => (q184 ◇ q183) ◇ t) (cg (fun t => (q184 ◇ q183) ◇ t) (apc177 q183 q183 (q184 ◇ q183) q183)))).trans (cg (fun t => ((q184 ◇ ((q184 ◇ q183) ◇ q184)) ◇ ((q184 ◇ q183) ◇ q184)) ◇ t) (cg (fun t => (q184 ◇ q183) ◇ t) (cg (fun t => (q184 ◇ q183) ◇ t) (apc146 (q183 ◇ q183) (q184 ◇ q183) q183))))).trans (cg (fun t => ((q184 ◇ ((q184 ◇ q183) ◇ q184)) ◇ ((q184 ◇ q183) ◇ q184)) ◇ t) (cg (fun t => (q184 ◇ q183) ◇ t) (apc177 (q184 ◇ q183) q184 (q183 ◇ (q183 ◇ q183)) q183)))).trans (cg (fun t => ((q184 ◇ ((q184 ◇ q183) ◇ q184)) ◇ ((q184 ◇ q183) ◇ q184)) ◇ t) (cg (fun t => (q184 ◇ q183) ◇ t) (cg (fun t => t ◇ (q183 ◇ (q184 ◇ q183))) (apc167 q183 q183 q184))))).trans (cg (fun t => ((q184 ◇ ((q184 ◇ q183) ◇ q184)) ◇ ((q184 ◇ q183) ◇ q184)) ◇ t) (cg (fun t => (q184 ◇ q183) ◇ t) (apc5 q183 q183 (q184 ◇ q183))))).trans (cg (fun t => ((q184 ◇ ((q184 ◇ q183) ◇ q184)) ◇ ((q184 ◇ q183) ◇ q184)) ◇ t) (apc140 (q183 ◇ q183) (q184 ◇ q183)))).trans (cg (fun t => ((q184 ◇ ((q184 ◇ q183) ◇ q184)) ◇ ((q184 ◇ q183) ◇ q184)) ◇ t) (apc177 (q184 ◇ q183) q183 (q184 ◇ q183) q183))).trans (cg (fun t => ((q184 ◇ ((q184 ◇ q183) ◇ q184)) ◇ ((q184 ◇ q183) ◇ q184)) ◇ t) (apc167 q183 q184 (q183 ◇ (q184 ◇ q183))))).trans (cg (fun t => ((q184 ◇ ((q184 ◇ q183) ◇ q184)) ◇ ((q184 ◇ q183) ◇ q184)) ◇ t) (cg (fun t => t ◇ q184) (apc146 q184 (q184 ◇ q183) q183)))).trans (cg (fun t => ((q184 ◇ ((q184 ◇ q183) ◇ q184)) ◇ ((q184 ◇ q183) ◇ q184)) ◇ t) (cg (fun t => t ◇ q184) (apc180 q183 q184)))).trans (cg (fun t => ((q184 ◇ ((q184 ◇ q183) ◇ q184)) ◇ ((q184 ◇ q183) ◇ q184)) ◇ t) (apc173 q183 q184))).trans (apc164 ((q184 ◇ q183) ◇ q184) q184 q184)).trans (apc167 q184 (q184 ◇ q183) q184)).symm).trans ((((cg (fun t => t ◇ ((q184 ◇ q183) ◇ ((q184 ◇ q183) ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183))))) (apc21 q183 q184 (q184 ◇ q183))).symm).trans (apc187 ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183)) (q184 ◇ q183))).trans ((((((((((((((((((((((((cg (fun t => t ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183))) (cg (fun t => t ◇ ((q184 ◇ q183) ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183)))) (cg (fun t => t ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183))) (apc177 q183 q183 (q184 ◇ q183) q183)))).trans (cg (fun t => t ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183))) (cg (fun t => t ◇ ((q184 ◇ q183) ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183)))) (cg (fun t => t ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183))) (apc146 (q183 ◇ q183) (q184 ◇ q183) q183))))).trans (cg (fun t => t ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183))) (cg (fun t => t ◇ ((q184 ◇ q183) ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183)))) (cg (fun t => ((q183 ◇ (q183 ◇ q183)) ◇ (q184 ◇ q183)) ◇ t) (apc177 q183 q183 (q184 ◇ q183) q183))))).trans (cg (fun t => t ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183))) (cg (fun t => t ◇ ((q184 ◇ q183) ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183)))) (cg (fun t => ((q183 ◇ (q183 ◇ q183)) ◇ (q184 ◇ q183)) ◇ t) (apc146 (q183 ◇ q183) (q184 ◇ q183) q183))))).trans (cg (fun t => t ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183))) (cg (fun t => (((q183 ◇ (q183 ◇ q183)) ◇ (q184 ◇ q183)) ◇ ((q183 ◇ (q183 ◇ q183)) ◇ (q184 ◇ q183))) ◇ t) (cg (fun t => (q184 ◇ q183) ◇ t) (apc177 q183 q183 (q184 ◇ q183) q183))))).trans (cg (fun t => t ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183))) (cg (fun t => (((q183 ◇ (q183 ◇ q183)) ◇ (q184 ◇ q183)) ◇ ((q183 ◇ (q183 ◇ q183)) ◇ (q184 ◇ q183))) ◇ t) (cg (fun t => (q184 ◇ q183) ◇ t) (apc146 (q183 ◇ q183) (q184 ◇ q183) q183))))).trans (cg (fun t => t ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183))) (cg (fun t => (((q183 ◇ (q183 ◇ q183)) ◇ (q184 ◇ q183)) ◇ ((q183 ◇ (q183 ◇ q183)) ◇ (q184 ◇ q183))) ◇ t) (apc177 (q184 ◇ q183) q184 (q183 ◇ (q183 ◇ q183)) q183)))).trans (cg (fun t => t ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183))) (cg (fun t => (((q183 ◇ (q183 ◇ q183)) ◇ (q184 ◇ q183)) ◇ ((q183 ◇ (q183 ◇ q183)) ◇ (q184 ◇ q183))) ◇ t) (cg (fun t => t ◇ (q183 ◇ (q184 ◇ q183))) (apc167 q183 q183 q184))))).trans (cg (fun t => t ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183))) (cg (fun t => (((q183 ◇ (q183 ◇ q183)) ◇ (q184 ◇ q183)) ◇ ((q183 ◇ (q183 ◇ q183)) ◇ (q184 ◇ q183))) ◇ t) (apc5 q183 q183 (q184 ◇ q183))))).trans (cg (fun t => t ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183))) (cg (fun t => t ◇ ((q183 ◇ q183) ◇ (q183 ◇ q183))) (apc177 (q184 ◇ q183) (q183 ◇ (q183 ◇ q183)) (q183 ◇ (q183 ◇ q183)) (q184 ◇ q183))))).trans (cg (fun t => t ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183))) (cg (fun t => t ◇ ((q183 ◇ q183) ◇ (q183 ◇ q183))) (cg (fun t => t ◇ ((q184 ◇ q183) ◇ (q184 ◇ q183))) (apc167 q183 q183 (q183 ◇ (q183 ◇ q183))))))).trans (cg (fun t => t ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183))) (cg (fun t => t ◇ ((q183 ◇ q183) ◇ (q183 ◇ q183))) (cg (fun t => t ◇ ((q184 ◇ q183) ◇ (q184 ◇ q183))) (cg (fun t => t ◇ q183) (apc146 q183 (q183 ◇ q183) q183)))))).trans (cg (fun t => t ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183))) (cg (fun t => t ◇ ((q183 ◇ q183) ◇ (q183 ◇ q183))) (cg (fun t => t ◇ ((q184 ◇ q183) ◇ (q184 ◇ q183))) (apc151 q183 q183))))).trans (cg (fun t => t ◇ ((q183 ◇ q183) ◇ ((q184 ◇ q183) ◇ q183))) (cg (fun t => t ◇ ((q183 ◇ q183) ◇ (q183 ◇ q183))) (apc140 (q184 ◇ q183) q183)))).trans (cg (fun t => (((q184 ◇ q183) ◇ (q183 ◇ q183)) ◇ ((q183 ◇ q183) ◇ (q183 ◇ q183))) ◇ t) (apc177 q183 q183 (q184 ◇ q183) q183))).trans (cg (fun t => (((q184 ◇ q183) ◇ (q183 ◇ q183)) ◇ ((q183 ◇ q183) ◇ (q183 ◇ q183))) ◇ t) (apc146 (q183 ◇ q183) (q184 ◇ q183) q183))).trans (cg (fun t => t ◇ ((q183 ◇ (q183 ◇ q183)) ◇ (q184 ◇ q183))) (apc169 (q183 ◇ q183) q183 ((q184 ◇ q183) ◇ (q183 ◇ q183))))).trans (cg (fun t => t ◇ ((q183 ◇ (q183 ◇ q183)) ◇ (q184 ◇ q183))) (cg (fun t => t ◇ q183) (apc162 (q184 ◇ q183) q183)))).trans (cg (fun t => t ◇ ((q183 ◇ (q183 ◇ q183)) ◇ (q184 ◇ q183))) (apc164 q183 q183 q184))).trans (cg (fun t => t ◇ ((q183 ◇ (q183 ◇ q183)) ◇ (q184 ◇ q183))) (apc140 q183 q184))).trans (apc177 (q184 ◇ q183) q183 (q183 ◇ (q183 ◇ q183)) (q184 ◇ q184))).trans (cg (fun t => t ◇ ((q184 ◇ q184) ◇ (q184 ◇ q183))) (apc167 q183 q183 q183))).trans (apc164 q183 ((q184 ◇ q184) ◇ (q184 ◇ q183)) q183)).trans (cg (fun t => q183 ◇ t) (apc173 q184 q183))))
  exact (calc
    (x ◇ x)=(x ◇ x):=rfl
    _=(y ◇ (z ◇ ((y ◇ x) ◇ z))):=((apc167 z (y ◇ x) y).trans (apc188 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19010_to_42551 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19010_to_42551
