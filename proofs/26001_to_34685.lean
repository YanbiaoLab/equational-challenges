-- Equation26001 → Equation34685
-- Recorded verdict: true
-- Premise: x = (y ◇ ((x ◇ y) ◇ y)) ◇ (z ◇ z)
-- Conclusion: x = ((x ◇ y) ◇ ((z ◇ z) ◇ w)) ◇ x
-- Original submission SHA-256: 7d17cc51ed2578099e99758621ba19111f817ae26fbddded461482d72f71c63f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ ((x ◇ y) ◇ y)) ◇ (z ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((x ◇ y) ◇ ((z ◇ z) ◇ w)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc0:=fun (x y z:G)=>by
    exact ((h x y z).symm).trans (h x x x)
  have apc1:=fun (x y z:G)=>by
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2:=fun (q0 q1 q2 q3:G)=>by
    exact ((cg (fun t => t ◇ (q3 ◇ q3)) (cg (fun t => (q2 ◇ q2) ◇ t) (cg (fun t => t ◇ (q2 ◇ q2)) ((h q0 q1 q2).symm)))).symm).trans ((h (q1 ◇ ((q0 ◇ q1) ◇ q1)) (q2 ◇ q2) q3).symm)
  have apc3:=fun (q0 q1 q2 q3:G)=>by
    exact ((apc2 q0 q1 q0 q0).symm).trans (apc2 q0 q0 q0 q0)
  have apc4:=fun (q4 q5 q6:G)=>by
    exact ((apc2 (q6 ◇ (q5 ◇ q5)) q4 q5 q4).symm).trans ((h q6 (q5 ◇ q5) q4).symm)
  have apc5:=fun (q7 q8 q9:G)=>by
    exact ((cg (fun t => t ◇ (q9 ◇ q9)) (apc4 q7 q7 q8)).symm).trans ((h (q8 ◇ (q7 ◇ q7)) q7 q9).symm)
  have apc6:=fun (q7 q8 q9:G)=>by
    exact (((apc5 q7 q8 q7).symm).trans (apc5 q8 q8 q7)).symm
  have apc7:=fun (q10 q11 q12 q13:G)=>by
    exact ((cg (fun t => q13 ◇ t) (apc5 q10 (q11 ◇ q11) q11)).symm).trans (apc5 q12 q13 (q11 ◇ q11))
  have apc8:=fun (q14 q15 q16:G)=>by
    exact (((apc7 q14 q14 q15 (q14 ◇ q14)).symm).trans (apc6 q16 (q14 ◇ q14) q14)).symm
  have apc9:=fun (q14 q15 q16:G)=>by
    exact ((apc8 q14 q15 q14).symm).trans (apc8 q14 q14 q14)
  have apc12:=fun (q17 q18:G)=>by
    exact ((cg (fun t => t ◇ (q18 ◇ q18)) (apc9 q17 q17 ((q17 ◇ q17) ◇ (q17 ◇ q17)))).symm).trans (((cg (fun t => t ◇ (q18 ◇ q18)) (apc7 q17 (q17 ◇ q17) q17 (q17 ◇ q17))).symm).trans ((h (q17 ◇ q17) (q17 ◇ q17) q18).symm))
  have apc13:=fun (q19 q20:G)=>by
    exact (((cg (fun t => (q20 ◇ q20) ◇ t) (apc9 q19 q20 ((q19 ◇ q19) ◇ (q20 ◇ q20)))).trans (apc9 q20 (q19 ◇ q19) ((q20 ◇ q20) ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))))).symm).trans ((((cg (fun t => (q20 ◇ q20) ◇ t) (cg (fun t => t ◇ (q20 ◇ q20)) (apc12 q19 q20))).symm).trans (apc3 ((q19 ◇ q19) ◇ (q19 ◇ q19)) (q20 ◇ q20) q19 q19)).trans (((cg (fun t => ((q19 ◇ q19) ◇ (q19 ◇ q19)) ◇ t) (cg (fun t => t ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) (apc12 q19 (q19 ◇ q19)))).trans (cg (fun t => ((q19 ◇ q19) ◇ (q19 ◇ q19)) ◇ t) (apc9 q19 (q19 ◇ q19) ((q19 ◇ q19) ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19)))))).trans (apc12 q19 (q19 ◇ q19))))
  have apc14:=fun (q19 q20:G)=>by
    exact (((apc13 q19 q20).symm).trans (apc13 q20 q20)).symm
  have apc23:=fun (q21 q22 q23:G)=>by
    exact ((cg (fun t => t ◇ (q23 ◇ q23)) (apc5 q21 (q22 ◇ q22) q22)).symm).trans (apc12 q22 q23)
  have apc24:=fun (q24 q25:G)=>by
    exact (((cg (fun t => (q25 ◇ q25) ◇ t) (apc5 q24 (q25 ◇ q25) q25)).symm).trans (apc6 q24 (q25 ◇ q25) q24)).trans (apc9 q25 q24 ((q25 ◇ q25) ◇ (q24 ◇ q24)))
  have apc25:=fun (q26:G)=>by
    exact (((((cg (fun t => (((q26 ◇ q26) ◇ (q26 ◇ q26)) ◇ (q26 ◇ q26)) ◇ t) (cg (fun t => (((q26 ◇ q26) ◇ (q26 ◇ q26)) ◇ ((q26 ◇ q26) ◇ (q26 ◇ q26))) ◇ t) (apc23 q26 q26 q26))).trans (cg (fun t => (((q26 ◇ q26) ◇ (q26 ◇ q26)) ◇ (q26 ◇ q26)) ◇ t) (cg (fun t => t ◇ (q26 ◇ q26)) (apc23 q26 q26 (q26 ◇ q26))))).trans (cg (fun t => t ◇ ((q26 ◇ q26) ◇ (q26 ◇ q26))) (apc23 q26 q26 q26))).trans (apc9 q26 (q26 ◇ q26) ((q26 ◇ q26) ◇ ((q26 ◇ q26) ◇ (q26 ◇ q26))))).symm).trans (((cg (fun t => (((q26 ◇ q26) ◇ (q26 ◇ q26)) ◇ (q26 ◇ q26)) ◇ t) (cg (fun t => t ◇ (((q26 ◇ q26) ◇ (q26 ◇ q26)) ◇ (q26 ◇ q26))) (apc24 q26 (q26 ◇ q26)))).symm).trans (apc4 (((q26 ◇ q26) ◇ (q26 ◇ q26)) ◇ (q26 ◇ q26)) q26 (q26 ◇ q26)))
  have apc26:=fun (q26 q14 q15 q16:G)=>by
    exact (apc9 q14 q15 q14).trans (apc25 q14)
  have apc29:=fun (q27 q28 q29:G)=>by
    exact ((cg (fun t => t ◇ (q29 ◇ q29)) (cg (fun t => q28 ◇ t) (cg (fun t => t ◇ q28) (apc14 q27 q28)))).symm).trans ((h q28 q28 q29).symm)
  have apc30:=fun (q30 q31 q32 q33:G)=>by
    exact ((((cg (fun t => t ◇ (q33 ◇ q33)) (cg (fun t => (q32 ◇ q32) ◇ t) ((h q30 q30 q32).symm))).symm).trans (apc2 (q30 ◇ ((q30 ◇ q30) ◇ q30)) q31 q32 q33)).trans (cg (fun t => q31 ◇ t) (cg (fun t => t ◇ q31) (cg (fun t => t ◇ q31) (apc3 q30 q30 (q30 ◇ ((q30 ◇ q30) ◇ q30)) (q30 ◇ ((q30 ◇ q30) ◇ q30))))))).symm
  have apc31:=fun (q30 q31 q32 q33:G)=>by
    exact ((apc30 q30 q30 q32 q33).symm).trans (apc30 q30 q30 q30 q30)
  have apc32:=fun (q34 q35:G)=>by
    exact (((apc4 q34 q34 ((q34 ◇ q34) ◇ q34)).symm).trans (((cg (fun t => q34 ◇ t) (cg (fun t => t ◇ q34) (cg (fun t => t ◇ q34) (apc31 q34 q34 q35 q34)))).symm).trans (apc4 q34 q34 ((q35 ◇ q35) ◇ q34)))).symm
  have apc33:=fun (q36 q37 q38 q39:G)=>by
    exact ((((apc30 q38 q36 q36 q37).symm).trans (apc30 q38 q36 q36 q39)).trans (cg (fun t => t ◇ (q39 ◇ q39)) (apc32 q38 q36))).symm
  have apc34:=fun (q40 q41 q42 q43:G)=>by
    exact ((cg (fun t => (q41 ◇ q41) ◇ t) (cg (fun t => t ◇ (q40 ◇ q40)) (apc29 q42 q42 q41))).symm).trans ((((cg (fun t => (q41 ◇ q41) ◇ t) (apc5 q40 ((q42 ◇ ((q42 ◇ q42) ◇ q42)) ◇ (q41 ◇ q41)) q41)).symm).trans (apc30 q42 (q41 ◇ q41) q40 q43)).trans (cg (fun t => t ◇ (q43 ◇ q43)) (apc32 q42 q40)))
  have apc35:=fun (q41 q42 q43:G)=>by
    exact ((cg (fun t => (q41 ◇ q41) ◇ t) (cg (fun t => t ◇ (q41 ◇ q41)) (apc29 q42 q42 q41))).symm).trans ((((cg (fun t => (q41 ◇ q41) ◇ t) (cg (fun t => t ◇ (q41 ◇ q41)) (apc5 q41 (q42 ◇ ((q42 ◇ q42) ◇ q42)) q41))).symm).trans (apc30 q42 (q41 ◇ q41) q41 q43)).trans (cg (fun t => t ◇ (q43 ◇ q43)) (apc32 q42 q41)))
  have apc39:=fun (q30 q31 q32 q33 q34 q35:G)=>by
    exact ((cg (fun t => t ◇ (q33 ◇ q33)) (apc32 q30 q30)).symm).trans (apc31 q30 q30 q30 q33)
  have apc41:=fun (q44 q45:G)=>by
    exact (((cg (fun t => (q44 ◇ q44) ◇ t) ((apc6 q44 q45 q44).symm)).symm).trans (apc34 q44 q44 q45 q44)).trans (apc39 q45 (((q45 ◇ q45) ◇ q45) ◇ (q44 ◇ q44)) (((q45 ◇ q45) ◇ q45) ◇ (q44 ◇ q44)) q44 (((q45 ◇ q45) ◇ q45) ◇ (q44 ◇ q44)) (((q45 ◇ q45) ◇ q45) ◇ (q44 ◇ q44)))
  have apc44:=fun (q41 q42 q43:G)=>by
    exact ((apc35 q41 q42 q41).trans ((apc35 q42 q42 q41).symm)).trans (apc41 q42 q42)
  have apc46:=fun (q46 q47 q48:G)=>by
    exact (((apc44 q46 q48 ((q46 ◇ q46) ◇ (q48 ◇ (q46 ◇ q46)))).symm).trans ((apc35 q46 q48 q46).trans ((apc34 q46 q47 q48 q46).symm))).symm
  have apc47:=fun (q49 q50 q51 q52 q53:G)=>by
    exact (((cg (fun t => t ◇ (q53 ◇ q53)) (cg (fun t => t ◇ q52) (apc14 q49 q52))).symm).trans (apc33 q50 q51 q52 q53)).symm
  have apc49:=fun (q54 q55:G)=>by
    exact ((cg (fun t => t ◇ (q55 ◇ q55)) (apc46 q54 q54 q54)).symm).trans (((cg (fun t => t ◇ (q55 ◇ q55)) (cg (fun t => (q54 ◇ q54) ◇ t) (cg (fun t => t ◇ (q54 ◇ q54)) (apc1 q54 q54 q54)))).symm).trans ((h (q54 ◇ ((q54 ◇ q54) ◇ q54)) (q54 ◇ q54) q55).symm))
  have apc50:=fun (q49 q50 q51 q52 q53:G)=>by
    exact (((apc47 q49 q50 q49 q52 q53).symm).trans (apc47 q50 q50 q49 q52 q50)).symm
  have apc91:=fun (q56 q57 q58 q59:G)=>by
    exact ((cg (fun t => t ◇ (q59 ◇ q59)) (apc50 q56 q58 q56 q58 q57)).symm).trans (apc49 q58 q59)
  have apc149:=fun (q60 q6 q61:G)=>by
    exact (((cg (fun t => t ◇ (q61 ◇ q61)) (cg (fun t => ((q60 ◇ q6) ◇ q6) ◇ t) (cg (fun t => t ◇ ((q60 ◇ q6) ◇ q6)) (cg (fun t => t ◇ (q60 ◇ q60)) (apc46 q60 q60 q60))))).trans (cg (fun t => t ◇ (q61 ◇ q61)) (cg (fun t => ((q60 ◇ q6) ◇ q6) ◇ t) (cg (fun t => t ◇ ((q60 ◇ q6) ◇ q6)) (apc91 q60 q60 q60 q60))))).symm).trans (((cg (fun t => t ◇ (q61 ◇ q61)) (cg (fun t => ((q60 ◇ q6) ◇ q6) ◇ t) (cg (fun t => t ◇ ((q60 ◇ q6) ◇ q6)) ((apc2 q60 q6 q60 q60).symm)))).symm).trans ((h q6 ((q60 ◇ q6) ◇ q6) q61).symm))
  have apc150:=fun (q62 q63:G)=>by
    exact (((((cg (fun t => t ◇ (q62 ◇ q62)) (cg (fun t => (((q62 ◇ q62) ◇ q63) ◇ q63) ◇ t) (cg (fun t => t ◇ (((q62 ◇ q62) ◇ q63) ◇ q63)) (cg (fun t => (q62 ◇ q62) ◇ t) (cg (fun t => t ◇ (q62 ◇ q62)) (apc26 ((q62 ◇ q62) ◇ (q62 ◇ q62)) q62 q62 ((q62 ◇ q62) ◇ (q62 ◇ q62)))))))).trans (cg (fun t => t ◇ (q62 ◇ q62)) (cg (fun t => (((q62 ◇ q62) ◇ q63) ◇ q63) ◇ t) (cg (fun t => t ◇ (((q62 ◇ q62) ◇ q63) ◇ q63)) (cg (fun t => (q62 ◇ q62) ◇ t) (apc26 ((q62 ◇ q62) ◇ (q62 ◇ q62)) q62 q62 ((q62 ◇ q62) ◇ (q62 ◇ q62)))))))).trans (cg (fun t => t ◇ (q62 ◇ q62)) (cg (fun t => (((q62 ◇ q62) ◇ q63) ◇ q63) ◇ t) (cg (fun t => t ◇ (((q62 ◇ q62) ◇ q63) ◇ q63)) (apc26 ((q62 ◇ q62) ◇ (q62 ◇ q62)) q62 q62 ((q62 ◇ q62) ◇ (q62 ◇ q62))))))).trans (apc29 q62 (((q62 ◇ q62) ◇ q63) ◇ q63) q62)).symm).trans (((cg (fun t => t ◇ (q62 ◇ q62)) (cg (fun t => (((q62 ◇ q62) ◇ q63) ◇ q63) ◇ t) (cg (fun t => t ◇ (((q62 ◇ q62) ◇ q63) ◇ q63)) (cg (fun t => (q62 ◇ q62) ◇ t) (apc5 q62 ((q62 ◇ q62) ◇ (q62 ◇ q62)) q62))))).symm).trans (apc149 (q62 ◇ q62) q63 q62))
  have apc151:=fun (q64 q65 q66:G)=>by
    exact ((cg (fun t => t ◇ (q66 ◇ q66)) (cg (fun t => q65 ◇ t) (cg (fun t => t ◇ q65) (apc150 q64 q65)))).symm).trans ((h ((q64 ◇ q64) ◇ q65) q65 q66).symm)
  have apc152:=fun (q67 q68:G)=>by
    exact (apc151 q67 q68 q67).trans (apc32 q68 q67)
  have apc153:=fun (q69:G)=>by
    exact (((((cg (fun t => t ◇ (q69 ◇ q69)) (cg (fun t => ((q69 ◇ q69) ◇ q69) ◇ t) (cg (fun t => (q69 ◇ ((q69 ◇ q69) ◇ q69)) ◇ t) (apc152 q69 q69)))).trans (cg (fun t => t ◇ (q69 ◇ q69)) (apc3 q69 ((q69 ◇ q69) ◇ q69) (((q69 ◇ q69) ◇ q69) ◇ ((q69 ◇ ((q69 ◇ q69) ◇ q69)) ◇ ((q69 ◇ q69) ◇ q69))) (((q69 ◇ q69) ◇ q69) ◇ ((q69 ◇ ((q69 ◇ q69) ◇ q69)) ◇ ((q69 ◇ q69) ◇ q69)))))).trans (apc29 q69 q69 q69)).symm).trans (((cg (fun t => t ◇ (q69 ◇ q69)) (cg (fun t => t ◇ ((q69 ◇ ((q69 ◇ q69) ◇ q69)) ◇ ((q69 ◇ (q69 ◇ q69)) ◇ (q69 ◇ q69)))) (apc152 q69 q69))).symm).trans (apc149 q69 (q69 ◇ q69) q69))).symm
  have apc154:=fun (q19 q20 q69:G)=>by
    exact ((apc153 q20).symm).trans ((apc14 q19 q20).trans (apc153 q19))
  exact (apc154 x x x).trans ((apc154 x (((x ◇ y) ◇ ((z ◇ z) ◇ w)) ◇ x) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_26001_to_34685 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_26001_to_34685
