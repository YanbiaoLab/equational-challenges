-- Equation28506 → Equation36377
-- Recorded verdict: true
-- Premise: x = (((x * y) * z) * x) * (y * z)
-- Conclusion: x = (((x * y) * y) * (z * x)) * y
-- Original submission SHA-256: fbbe87d3e41d4b6c6c7edf8a08c7cf135eb8a6e4ee3e38d5595c3da1e29ee79a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((x ◇ y) ◇ z) ◇ x) ◇ (y ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((x ◇ y) ◇ y) ◇ (z ◇ x)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc0:=fun (q0:G)=>by
    exact ((cg (fun t => t ◇ (q0 ◇ q0)) ((h q0 q0 q0).symm)).symm).trans ((h (q0 ◇ q0) q0 q0).symm)
  have apc1:=fun (x y z:G)=>by
    exact ((h x y z).symm).trans (h x x x)
  have apc2:=fun (x y z:G)=>by
    exact ((h x x x).trans (apc1 x x x)).symm
  have apc3:=fun (q1:G)=>by
    exact ((cg (fun t => (q1 ◇ ((q1 ◇ q1) ◇ q1)) ◇ t) (apc0 q1)).symm).trans (((cg (fun t => t ◇ (q1 ◇ (q1 ◇ q1))) (cg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (apc2 q1 q1 q1))).symm).trans ((h ((q1 ◇ q1) ◇ q1) q1 (q1 ◇ q1)).symm))
  have apc4:=fun (q2 q3:G)=>by
    exact ((cg (fun t => t ◇ ((q2 ◇ q2) ◇ q3)) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ q3) (apc0 q2)))).symm).trans ((h q2 (q2 ◇ q2) q3).symm)
  have apc5:=fun (q2 q4:G)=>by
    exact ((cg (fun t => (((q2 ◇ q4) ◇ (q4 ◇ q4)) ◇ q2) ◇ t) (apc0 q4)).symm).trans ((h q2 q4 (q4 ◇ q4)).symm)
  have apc6:=fun (q5:G)=>by
    exact ((cg (fun t => t ◇ ((q5 ◇ q5) ◇ q5)) (apc5 q5 q5)).symm).trans ((h (q5 ◇ q5) (q5 ◇ q5) q5).symm)
  have apc7:=fun (q1 q5:G)=>by
    exact ((cg (fun t => t ◇ (q1 ◇ q1)) (apc6 q1)).symm).trans (apc3 q1)
  have apc9:=fun (q6:G)=>by
    exact ((cg (fun t => q6 ◇ t) (cg (fun t => t ◇ q6) (apc7 q6 ((q6 ◇ q6) ◇ (q6 ◇ q6))))).symm).trans (((cg (fun t => t ◇ (((q6 ◇ q6) ◇ (q6 ◇ q6)) ◇ q6)) (apc5 q6 q6)).symm).trans (apc4 (q6 ◇ q6) q6))
  have apc10:=fun (q7 q8 q9:G)=>by
    exact ((cg (fun t => t ◇ (q9 ◇ (q7 ◇ q8))) (cg (fun t => t ◇ ((q9 ◇ q7) ◇ q8)) ((h q9 q7 q8).symm))).symm).trans ((h ((q9 ◇ q7) ◇ q8) q9 (q7 ◇ q8)).symm)
  have apc11:=fun (q10:G)=>by
    exact ((cg (fun t => ((q10 ◇ q10) ◇ q10) ◇ t) (apc7 q10 ((q10 ◇ q10) ◇ (q10 ◇ q10)))).symm).trans ((((cg (fun t => t ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10))) (apc7 q10 q10)).symm).trans (apc7 (q10 ◇ q10) q10)).trans (cg (fun t => t ◇ (q10 ◇ q10)) (apc7 q10 ((q10 ◇ q10) ◇ (q10 ◇ q10)))))
  have apc13:=fun (q11 q12:G)=>by
    exact ((cg (fun t => t ◇ (((q11 ◇ q11) ◇ q11) ◇ q12)) (cg (fun t => t ◇ q11) (cg (fun t => t ◇ q12) (apc6 q11)))).symm).trans ((h q11 ((q11 ◇ q11) ◇ q11) q12).symm)
  have apc14:=fun (q13:G)=>by
    exact (((cg (fun t => (((q13 ◇ q13) ◇ q13) ◇ q13) ◇ t) (apc13 q13 q13)).symm).trans (apc0 (((q13 ◇ q13) ◇ q13) ◇ q13))).trans (apc13 q13 q13)
  have apc17:=fun (q14:G)=>by
    exact (((cg (fun t => t ◇ ((((q14 ◇ q14) ◇ q14) ◇ q14) ◇ (((q14 ◇ q14) ◇ q14) ◇ q14))) (cg (fun t => t ◇ (((q14 ◇ q14) ◇ q14) ◇ q14)) (apc9 q14))).trans (cg (fun t => ((q14 ◇ q14) ◇ (((q14 ◇ q14) ◇ q14) ◇ q14)) ◇ t) (apc13 q14 q14))).symm).trans (((cg (fun t => t ◇ ((((q14 ◇ q14) ◇ q14) ◇ q14) ◇ (((q14 ◇ q14) ◇ q14) ◇ q14))) (cg (fun t => t ◇ (((q14 ◇ q14) ◇ q14) ◇ q14)) (cg (fun t => t ◇ (((q14 ◇ q14) ◇ q14) ◇ q14)) (apc13 q14 q14)))).symm).trans (apc2 (((q14 ◇ q14) ◇ q14) ◇ q14) q14 q14))
  have apc18:=fun (q15 q7 q8 q16:G)=>by
    exact ((cg (fun t => (((q16 ◇ (((q15 ◇ q7) ◇ q8) ◇ q15)) ◇ (q7 ◇ q8)) ◇ q16) ◇ t) ((h q15 q7 q8).symm)).symm).trans ((h q16 (((q15 ◇ q7) ◇ q8) ◇ q15) (q7 ◇ q8)).symm)
  have apc19:=fun (q17 q18:G)=>by
    exact (((cg (fun t => t ◇ (q17 ◇ q17)) (cg (fun t => t ◇ q18) (cg (fun t => t ◇ ((((q17 ◇ q17) ◇ q17) ◇ q17) ◇ q17)) (cg (fun t => q18 ◇ t) (apc2 q17 ((((q17 ◇ q17) ◇ q17) ◇ q17) ◇ (q17 ◇ q17)) ((((q17 ◇ q17) ◇ q17) ◇ q17) ◇ (q17 ◇ q17))))))).trans (cg (fun t => t ◇ (q17 ◇ q17)) (cg (fun t => t ◇ q18) (cg (fun t => (q18 ◇ q17) ◇ t) (apc14 q17))))).symm).trans (((cg (fun t => t ◇ (q17 ◇ q17)) (cg (fun t => t ◇ q18) (cg (fun t => t ◇ ((((q17 ◇ q17) ◇ q17) ◇ q17) ◇ q17)) (cg (fun t => q18 ◇ t) (cg (fun t => t ◇ (q17 ◇ q17)) (apc17 q17)))))).symm).trans (apc18 (q17 ◇ q17) (((q17 ◇ q17) ◇ q17) ◇ q17) q17 q18))
  have apc20:=fun (q19 q20:G)=>by
    exact ((cg (fun t => t ◇ (q20 ◇ ((q20 ◇ q20) ◇ q19))) (cg (fun t => t ◇ ((q20 ◇ q20) ◇ q19)) (apc4 q20 q19))).symm).trans ((h ((q20 ◇ q20) ◇ q19) q20 ((q20 ◇ q20) ◇ q19)).symm)
  have apc26:=fun (q21 q22:G)=>by
    exact (((cg (fun t => ((q22 ◇ q22) ◇ q21) ◇ t) (apc20 q21 q22)).symm).trans ((((cg (fun t => t ◇ ((q22 ◇ ((q22 ◇ q22) ◇ q21)) ◇ (q22 ◇ ((q22 ◇ q22) ◇ q21)))) (apc20 q21 q22)).symm).trans (apc7 (q22 ◇ ((q22 ◇ q22) ◇ q21)) q21)).trans (cg (fun t => t ◇ (q22 ◇ ((q22 ◇ q22) ◇ q21))) (apc20 q21 q22)))).symm
  have apc27:=fun (q15 q7 q8 q0:G)=>by
    exact ((cg (fun t => t ◇ ((q7 ◇ q8) ◇ q0)) (cg (fun t => t ◇ (((q15 ◇ q7) ◇ q8) ◇ q15)) (cg (fun t => t ◇ q0) ((h q15 q7 q8).symm)))).symm).trans ((h (((q15 ◇ q7) ◇ q8) ◇ q15) (q7 ◇ q8) q0).symm)
  have apc28:=fun (q23 q24:G)=>by
    exact (((cg (fun t => (((q23 ◇ q23) ◇ q24) ◇ ((((q23 ◇ q23) ◇ q23) ◇ q23) ◇ (q23 ◇ q23))) ◇ t) (cg (fun t => t ◇ q24) (apc14 q23))).trans (cg (fun t => t ◇ (q23 ◇ q24)) (cg (fun t => ((q23 ◇ q23) ◇ q24) ◇ t) (apc19 q23 q23)))).symm).trans ((((cg (fun t => t ◇ (((((q23 ◇ q23) ◇ q23) ◇ q23) ◇ q23) ◇ q24)) (cg (fun t => ((q23 ◇ q23) ◇ q24) ◇ t) (cg (fun t => t ◇ (q23 ◇ q23)) (apc17 q23)))).symm).trans (apc27 (q23 ◇ q23) (((q23 ◇ q23) ◇ q23) ◇ q23) q23 q24)).trans ((cg (fun t => t ◇ (q23 ◇ q23)) (apc17 q23)).trans (apc19 q23 q23)))
  have apc30:=fun (q25 q26:G)=>by
    exact ((cg (fun t => t ◇ ((((q25 ◇ q25) ◇ q25) ◇ q25) ◇ q26)) (cg (fun t => t ◇ q25) (cg (fun t => t ◇ q26) (apc9 q25)))).symm).trans ((h q25 (((q25 ◇ q25) ◇ q25) ◇ q25) q26).symm)
  have apc32:=fun (q27 q28:G)=>by
    exact ((cg (fun t => ((q27 ◇ q28) ◇ (((q27 ◇ q27) ◇ q27) ◇ q27)) ◇ t) (cg (fun t => t ◇ q28) (apc13 q27 q27))).symm).trans (((cg (fun t => t ◇ (((((q27 ◇ q27) ◇ q27) ◇ q27) ◇ (((q27 ◇ q27) ◇ q27) ◇ q27)) ◇ q28)) (cg (fun t => t ◇ (((q27 ◇ q27) ◇ q27) ◇ q27)) (cg (fun t => t ◇ q28) (apc13 q27 q27)))).symm).trans (apc4 (((q27 ◇ q27) ◇ q27) ◇ q27) q28))
  have apc38:=fun (q29 q30:G)=>by
    exact ((cg (fun t => t ◇ ((q29 ◇ q29) ◇ q30)) (cg (fun t => t ◇ (q29 ◇ q29)) (cg (fun t => t ◇ q30) (apc7 q29 q29)))).symm).trans ((h (q29 ◇ q29) (q29 ◇ q29) q30).symm)
  have apc42:=fun (q31 q32 q33:G)=>by
    exact ((cg (fun t => (((q33 ◇ (((q31 ◇ q32) ◇ (q32 ◇ q32)) ◇ q31)) ◇ (q32 ◇ q32)) ◇ q33) ◇ t) (apc5 q31 q32)).symm).trans ((h q33 (((q31 ◇ q32) ◇ (q32 ◇ q32)) ◇ q31) (q32 ◇ q32)).symm)
  have apc54:=fun (q34:G)=>by
    exact ((((cg (fun t => t ◇ ((((q34 ◇ q34) ◇ q34) ◇ q34) ◇ (((q34 ◇ q34) ◇ q34) ◇ q34))) (cg (fun t => t ◇ q34) (cg (fun t => (q34 ◇ q34) ◇ t) (cg (fun t => t ◇ (((q34 ◇ q34) ◇ q34) ◇ q34)) (cg (fun t => t ◇ (((q34 ◇ q34) ◇ q34) ◇ q34)) (apc13 q34 q34)))))).trans (cg (fun t => t ◇ ((((q34 ◇ q34) ◇ q34) ◇ q34) ◇ (((q34 ◇ q34) ◇ q34) ◇ q34))) (cg (fun t => t ◇ q34) (cg (fun t => (q34 ◇ q34) ◇ t) (cg (fun t => t ◇ (((q34 ◇ q34) ◇ q34) ◇ q34)) (apc9 q34)))))).trans (cg (fun t => (((q34 ◇ q34) ◇ ((q34 ◇ q34) ◇ (((q34 ◇ q34) ◇ q34) ◇ q34))) ◇ q34) ◇ t) (apc13 q34 q34))).symm).trans (((cg (fun t => (((q34 ◇ q34) ◇ ((((((q34 ◇ q34) ◇ q34) ◇ q34) ◇ (((q34 ◇ q34) ◇ q34) ◇ q34)) ◇ (((q34 ◇ q34) ◇ q34) ◇ q34)) ◇ (((q34 ◇ q34) ◇ q34) ◇ q34))) ◇ q34) ◇ t) (apc9 (((q34 ◇ q34) ◇ q34) ◇ q34))).symm).trans (apc30 q34 ((((((q34 ◇ q34) ◇ q34) ◇ q34) ◇ (((q34 ◇ q34) ◇ q34) ◇ q34)) ◇ (((q34 ◇ q34) ◇ q34) ◇ q34)) ◇ (((q34 ◇ q34) ◇ q34) ◇ q34))))
  have apc56:=fun (q35 q19 q36:G)=>by
    exact ((cg (fun t => t ◇ (((q35 ◇ q35) ◇ q19) ◇ q36)) (cg (fun t => t ◇ (((q35 ◇ q35) ◇ q19) ◇ q35)) (cg (fun t => t ◇ q36) (apc4 q35 q19)))).symm).trans ((h (((q35 ◇ q35) ◇ q19) ◇ q35) ((q35 ◇ q35) ◇ q19) q36).symm)
  have apc64:=fun (q31 q32 q5:G)=>by
    exact ((cg (fun t => t ◇ ((q32 ◇ q32) ◇ q5)) (cg (fun t => t ◇ (((q31 ◇ q32) ◇ (q32 ◇ q32)) ◇ q31)) (cg (fun t => t ◇ q5) (apc5 q31 q32)))).symm).trans ((h (((q31 ◇ q32) ◇ (q32 ◇ q32)) ◇ q31) (q32 ◇ q32) q5).symm)
  have apc82:=fun (q37 q38:G)=>by
    exact ((cg (fun t => (q38 ◇ ((q38 ◇ q38) ◇ q37)) ◇ t) (apc26 q37 q38)).symm).trans ((((cg (fun t => (q38 ◇ ((q38 ◇ q38) ◇ q37)) ◇ t) (cg (fun t => t ◇ (q38 ◇ ((q38 ◇ q38) ◇ q37))) (apc20 q37 q38))).symm).trans (apc6 (q38 ◇ ((q38 ◇ q38) ◇ q37)))).trans (apc20 q37 q38))
  have apc83:=fun (q39 q40:G)=>by
    exact (((cg (fun t => ((((q39 ◇ q39) ◇ q39) ◇ q39) ◇ (q39 ◇ q40)) ◇ t) (cg (fun t => t ◇ (((((q39 ◇ q39) ◇ q39) ◇ q39) ◇ (((q39 ◇ q39) ◇ q39) ◇ q39)) ◇ q40)) (cg (fun t => t ◇ q40) (apc13 q39 q39)))).trans (cg (fun t => ((((q39 ◇ q39) ◇ q39) ◇ q39) ◇ (q39 ◇ q40)) ◇ t) (cg (fun t => (q39 ◇ q40) ◇ t) (cg (fun t => t ◇ q40) (apc13 q39 q39))))).symm).trans ((((cg (fun t => t ◇ ((((((q39 ◇ q39) ◇ q39) ◇ q39) ◇ (((q39 ◇ q39) ◇ q39) ◇ q39)) ◇ q40) ◇ (((((q39 ◇ q39) ◇ q39) ◇ q39) ◇ (((q39 ◇ q39) ◇ q39) ◇ q39)) ◇ q40))) (cg (fun t => (((q39 ◇ q39) ◇ q39) ◇ q39) ◇ t) (cg (fun t => t ◇ q40) (apc13 q39 q39)))).symm).trans (apc82 q40 (((q39 ◇ q39) ◇ q39) ◇ q39))).trans (cg (fun t => t ◇ q40) (apc13 q39 q39)))
  have apc95:=fun (q41 q42 q43:G)=>by
    exact ((cg (fun t => ((((q41 ◇ q42) ◇ q43) ◇ q41) ◇ (((((q41 ◇ q42) ◇ q43) ◇ q41) ◇ q42) ◇ q43)) ◇ t) ((h q41 q42 q43).symm)).symm).trans (apc10 q42 q43 (((q41 ◇ q42) ◇ q43) ◇ q41))
  have apc96:=fun (q44:G)=>by
    exact (((cg (fun t => t ◇ q44) (apc28 q44 ((q44 ◇ q44) ◇ (((q44 ◇ q44) ◇ q44) ◇ q44)))).symm).trans ((((cg (fun t => t ◇ q44) (cg (fun t => (((q44 ◇ q44) ◇ ((q44 ◇ q44) ◇ (((q44 ◇ q44) ◇ q44) ◇ q44))) ◇ q44) ◇ t) (cg (fun t => t ◇ ((q44 ◇ q44) ◇ (((q44 ◇ q44) ◇ q44) ◇ q44))) (apc54 q44)))).symm).trans (apc95 q44 q44 ((q44 ◇ q44) ◇ (((q44 ◇ q44) ◇ q44) ◇ q44)))).trans (cg (fun t => t ◇ ((q44 ◇ q44) ◇ (((q44 ◇ q44) ◇ q44) ◇ q44))) (apc54 q44)))).symm
  have apc97:=fun (q45:G)=>by
    exact (((((cg (fun t => (q45 ◇ q45) ◇ t) (cg (fun t => q45 ◇ t) (apc9 q45))).trans (cg (fun t => (q45 ◇ q45) ◇ t) (apc0 q45))).trans (apc7 q45 ((q45 ◇ q45) ◇ (q45 ◇ q45)))).symm).trans (((cg (fun t => t ◇ (q45 ◇ (q45 ◇ (((q45 ◇ q45) ◇ q45) ◇ q45)))) (apc96 q45)).symm).trans (apc10 q45 (((q45 ◇ q45) ◇ q45) ◇ q45) q45))).symm
  have apc98:=fun (q46:G)=>by
    exact (((cg (fun t => ((q46 ◇ q46) ◇ q46) ◇ t) (apc7 q46 ((q46 ◇ q46) ◇ (q46 ◇ q46)))).trans (apc11 q46)).symm).trans (((cg (fun t => t ◇ ((q46 ◇ q46) ◇ (q46 ◇ q46))) (apc97 q46)).symm).trans (apc10 q46 q46 (q46 ◇ q46)))
  have apc99:=fun (q10 q46:G)=>by
    exact (apc11 q10).trans (apc98 q10)
  have apc100:=fun (q47:G)=>by
    exact ((cg (fun t => t ◇ (((q47 ◇ q47) ◇ q47) ◇ q47)) (apc97 q47)).symm).trans (apc56 q47 q47 q47)
  have apc102:=fun (q48 q49:G)=>by
    exact (((((cg (fun t => t ◇ (((((q48 ◇ q48) ◇ q48) ◇ q48) ◇ (((q48 ◇ q48) ◇ q48) ◇ q48)) ◇ q49)) (cg (fun t => (((q48 ◇ q48) ◇ q48) ◇ q49) ◇ t) (cg (fun t => t ◇ ((q48 ◇ q48) ◇ q48)) (cg (fun t => (((q48 ◇ q48) ◇ q48) ◇ q48) ◇ t) (apc13 q48 q48))))).trans (cg (fun t => t ◇ (((((q48 ◇ q48) ◇ q48) ◇ q48) ◇ (((q48 ◇ q48) ◇ q48) ◇ q48)) ◇ q49)) (cg (fun t => (((q48 ◇ q48) ◇ q48) ◇ q49) ◇ t) (cg (fun t => t ◇ ((q48 ◇ q48) ◇ q48)) (apc14 q48))))).trans (cg (fun t => t ◇ (((((q48 ◇ q48) ◇ q48) ◇ q48) ◇ (((q48 ◇ q48) ◇ q48) ◇ q48)) ◇ q49)) (cg (fun t => (((q48 ◇ q48) ◇ q48) ◇ q49) ◇ t) (apc6 q48)))).trans (cg (fun t => ((((q48 ◇ q48) ◇ q48) ◇ q49) ◇ (q48 ◇ q48)) ◇ t) (cg (fun t => t ◇ q49) (apc13 q48 q48)))).symm).trans ((((cg (fun t => t ◇ (((((q48 ◇ q48) ◇ q48) ◇ q48) ◇ (((q48 ◇ q48) ◇ q48) ◇ q48)) ◇ q49)) (cg (fun t => (((q48 ◇ q48) ◇ q48) ◇ q49) ◇ t) (cg (fun t => t ◇ ((q48 ◇ q48) ◇ q48)) (cg (fun t => t ◇ ((((q48 ◇ q48) ◇ q48) ◇ q48) ◇ (((q48 ◇ q48) ◇ q48) ◇ q48))) (apc100 q48))))).symm).trans (apc64 ((q48 ◇ q48) ◇ q48) (((q48 ◇ q48) ◇ q48) ◇ q48) q49)).trans ((((cg (fun t => t ◇ ((q48 ◇ q48) ◇ q48)) (cg (fun t => t ◇ ((((q48 ◇ q48) ◇ q48) ◇ q48) ◇ (((q48 ◇ q48) ◇ q48) ◇ q48))) (apc100 q48))).trans (cg (fun t => t ◇ ((q48 ◇ q48) ◇ q48)) (cg (fun t => (((q48 ◇ q48) ◇ q48) ◇ q48) ◇ t) (apc13 q48 q48)))).trans (cg (fun t => t ◇ ((q48 ◇ q48) ◇ q48)) (apc14 q48))).trans (apc6 q48)))
  have apc114:=fun (q11 q50:G)=>by
    exact ((cg (fun t => t ◇ (q50 ◇ (((q11 ◇ q50) ◇ (q11 ◇ q50)) ◇ (q11 ◇ q50)))) (cg (fun t => t ◇ q11) (apc6 (q11 ◇ q50)))).symm).trans ((h q11 q50 (((q11 ◇ q50) ◇ (q11 ◇ q50)) ◇ (q11 ◇ q50))).symm)
  have apc121:=fun (q51 q52 q53:G)=>by
    exact ((cg (fun t => t ◇ ((((q51 ◇ q51) ◇ q51) ◇ q52) ◇ q53)) (cg (fun t => t ◇ (((q51 ◇ q51) ◇ q52) ◇ q51)) (cg (fun t => t ◇ q53) (apc13 q51 q52)))).symm).trans ((h (((q51 ◇ q51) ◇ q52) ◇ q51) (((q51 ◇ q51) ◇ q51) ◇ q52) q53).symm)
  have apc126:=fun (q54 q55 q56:G)=>by
    exact ((cg (fun t => t ◇ q55) (cg (fun t => t ◇ q56) (cg (fun t => (q56 ◇ (((q55 ◇ (q54 ◇ q54)) ◇ (q54 ◇ q54)) ◇ q55)) ◇ t) (apc7 q54 q54)))).symm).trans (apc18 q55 (q54 ◇ q54) (q54 ◇ q54) q56)
  have apc128:=fun (q57 q58:G)=>by
    exact ((cg (fun t => ((((q58 ◇ q58) ◇ q58) ◇ q58) ◇ (q58 ◇ ((q58 ◇ q58) ◇ q57))) ◇ t) (apc20 q57 q58)).symm).trans (apc83 q58 ((q58 ◇ q58) ◇ q57))
  have apc129:=fun (q59 q60:G)=>by
    exact ((((((cg (fun t => t ◇ (((q60 ◇ q60) ◇ q60) ◇ q60)) (cg (fun t => ((q60 ◇ ((q60 ◇ q60) ◇ q59)) ◇ (((q60 ◇ q60) ◇ q60) ◇ q60)) ◇ t) (cg (fun t => t ◇ ((q60 ◇ q60) ◇ q59)) (cg (fun t => t ◇ (q60 ◇ ((q60 ◇ q60) ◇ q59))) (cg (fun t => t ◇ (((q60 ◇ q60) ◇ q60) ◇ q60)) (apc128 q59 q60)))))).trans (cg (fun t => t ◇ (((q60 ◇ q60) ◇ q60) ◇ q60)) (cg (fun t => ((q60 ◇ ((q60 ◇ q60) ◇ q59)) ◇ (((q60 ◇ q60) ◇ q60) ◇ q60)) ◇ t) (cg (fun t => t ◇ ((q60 ◇ q60) ◇ q59)) (apc32 q60 ((q60 ◇ q60) ◇ q59)))))).trans (cg (fun t => t ◇ (((q60 ◇ q60) ◇ q60) ◇ q60)) (apc121 q60 q60 ((q60 ◇ q60) ◇ q59)))).trans (apc13 q60 q60)).symm).trans ((((cg (fun t => t ◇ (((q60 ◇ q60) ◇ q60) ◇ q60)) (cg (fun t => t ◇ ((((((((q60 ◇ q60) ◇ q60) ◇ q60) ◇ (q60 ◇ ((q60 ◇ q60) ◇ q59))) ◇ ((q60 ◇ q60) ◇ q59)) ◇ (((q60 ◇ q60) ◇ q60) ◇ q60)) ◇ (q60 ◇ ((q60 ◇ q60) ◇ q59))) ◇ ((q60 ◇ q60) ◇ q59))) (cg (fun t => t ◇ (((q60 ◇ q60) ◇ q60) ◇ q60)) (apc128 q59 q60)))).symm).trans (apc95 (((q60 ◇ q60) ◇ q60) ◇ q60) (q60 ◇ ((q60 ◇ q60) ◇ q59)) ((q60 ◇ q60) ◇ q59))).trans ((cg (fun t => t ◇ ((q60 ◇ q60) ◇ q59)) (cg (fun t => t ◇ (q60 ◇ ((q60 ◇ q60) ◇ q59))) (cg (fun t => t ◇ (((q60 ◇ q60) ◇ q60) ◇ q60)) (apc128 q59 q60)))).trans (cg (fun t => t ◇ ((q60 ◇ q60) ◇ q59)) (apc32 q60 ((q60 ◇ q60) ◇ q59)))))).symm
  have apc130:=fun (q61 q62:G)=>by
    exact ((((cg (fun t => ((((q61 ◇ q61) ◇ q61) ◇ (q61 ◇ q61)) ◇ (q61 ◇ q61)) ◇ t) (cg (fun t => t ◇ q62) (apc7 q61 ((q61 ◇ q61) ◇ (q61 ◇ q61))))).trans (cg (fun t => t ◇ (((q61 ◇ q61) ◇ q61) ◇ q62)) (cg (fun t => t ◇ (q61 ◇ q61)) (apc98 q61)))).trans (cg (fun t => t ◇ (((q61 ◇ q61) ◇ q61) ◇ q62)) (apc19 q61 q61))).symm).trans (((cg (fun t => t ◇ (((q61 ◇ q61) ◇ (q61 ◇ q61)) ◇ q62)) (cg (fun t => t ◇ (q61 ◇ q61)) (cg (fun t => t ◇ (q61 ◇ q61)) (apc7 q61 q61)))).symm).trans (apc129 q62 (q61 ◇ q61)))
  have apc131:=fun (q63 q64:G)=>by
    exact (((((cg (fun t => ((((q64 ◇ q64) ◇ q64) ◇ ((q64 ◇ q64) ◇ q64)) ◇ (q64 ◇ q64)) ◇ t) (cg (fun t => q64 ◇ t) (cg (fun t => t ◇ q63) (cg (fun t => t ◇ ((q64 ◇ q64) ◇ q64)) (apc99 q64 (((q64 ◇ q64) ◇ q64) ◇ ((q64 ◇ q64) ◇ q64))))))).trans (cg (fun t => ((((q64 ◇ q64) ◇ q64) ◇ ((q64 ◇ q64) ◇ q64)) ◇ (q64 ◇ q64)) ◇ t) (cg (fun t => q64 ◇ t) (cg (fun t => t ◇ q63) (apc4 q64 q64))))).trans (cg (fun t => t ◇ (q64 ◇ (q64 ◇ q63))) (cg (fun t => t ◇ (q64 ◇ q64)) (apc99 q64 (((q64 ◇ q64) ◇ q64) ◇ ((q64 ◇ q64) ◇ q64)))))).trans (cg (fun t => t ◇ (q64 ◇ (q64 ◇ q63))) (apc19 q64 q64))).symm).trans (((cg (fun t => t ◇ (q64 ◇ (((((q64 ◇ q64) ◇ q64) ◇ ((q64 ◇ q64) ◇ q64)) ◇ ((q64 ◇ q64) ◇ q64)) ◇ q63))) (cg (fun t => t ◇ (q64 ◇ q64)) (apc130 ((q64 ◇ q64) ◇ q64) q63))).symm).trans (apc102 q64 (((((q64 ◇ q64) ◇ q64) ◇ ((q64 ◇ q64) ◇ q64)) ◇ ((q64 ◇ q64) ◇ q64)) ◇ q63)))
  have apc132:=fun (q65 q66:G)=>by
    exact (((((cg (fun t => ((((q66 ◇ q66) ◇ q66) ◇ ((q66 ◇ q66) ◇ q66)) ◇ (q66 ◇ q66)) ◇ t) (cg (fun t => (q66 ◇ q66) ◇ t) (cg (fun t => t ◇ q65) (cg (fun t => t ◇ ((q66 ◇ q66) ◇ q66)) (apc99 q66 (((q66 ◇ q66) ◇ q66) ◇ ((q66 ◇ q66) ◇ q66))))))).trans (cg (fun t => ((((q66 ◇ q66) ◇ q66) ◇ ((q66 ◇ q66) ◇ q66)) ◇ (q66 ◇ q66)) ◇ t) (cg (fun t => (q66 ◇ q66) ◇ t) (cg (fun t => t ◇ q65) (apc4 q66 q66))))).trans (cg (fun t => t ◇ ((q66 ◇ q66) ◇ (q66 ◇ q65))) (cg (fun t => t ◇ (q66 ◇ q66)) (apc99 q66 (((q66 ◇ q66) ◇ q66) ◇ ((q66 ◇ q66) ◇ q66)))))).trans (cg (fun t => t ◇ ((q66 ◇ q66) ◇ (q66 ◇ q65))) (apc19 q66 q66))).symm).trans (((cg (fun t => t ◇ ((q66 ◇ q66) ◇ (((((q66 ◇ q66) ◇ q66) ◇ ((q66 ◇ q66) ◇ q66)) ◇ ((q66 ◇ q66) ◇ q66)) ◇ q65))) (cg (fun t => t ◇ (q66 ◇ q66)) (apc130 ((q66 ◇ q66) ◇ q66) q65))).symm).trans (apc38 q66 (((((q66 ◇ q66) ◇ q66) ◇ ((q66 ◇ q66) ◇ q66)) ◇ ((q66 ◇ q66) ◇ q66)) ◇ q65)))
  have apc133:=fun (q67 q68:G)=>by
    exact ((((cg (fun t => (q68 ◇ q68) ◇ t) (apc131 q67 q68)).trans (apc7 q68 ((q68 ◇ q68) ◇ (q68 ◇ q68)))).symm).trans (((cg (fun t => t ◇ (q68 ◇ (q68 ◇ (q68 ◇ q67)))) (apc132 q67 q68)).symm).trans (apc10 q68 (q68 ◇ q67) q68))).symm
  have apc134:=fun (q69 q70:G)=>by
    exact (((((((((cg (fun t => ((((q70 ◇ q70) ◇ q70) ◇ ((q70 ◇ q70) ◇ (q70 ◇ q69))) ◇ (q70 ◇ q70)) ◇ t) (cg (fun t => (q70 ◇ q69) ◇ t) (cg (fun t => t ◇ ((q70 ◇ q70) ◇ (q70 ◇ q69))) (cg (fun t => t ◇ ((q70 ◇ q70) ◇ (q70 ◇ q69))) (apc133 q69 q70))))).trans (cg (fun t => ((((q70 ◇ q70) ◇ q70) ◇ ((q70 ◇ q70) ◇ (q70 ◇ q69))) ◇ (q70 ◇ q70)) ◇ t) (cg (fun t => (q70 ◇ q69) ◇ t) (cg (fun t => t ◇ ((q70 ◇ q70) ◇ (q70 ◇ q69))) (cg (fun t => ((q70 ◇ q70) ◇ q70) ◇ t) (apc133 q69 q70)))))).trans (cg (fun t => t ◇ ((q70 ◇ q69) ◇ ((((q70 ◇ q70) ◇ q70) ◇ ((q70 ◇ q70) ◇ q70)) ◇ ((q70 ◇ q70) ◇ (q70 ◇ q69))))) (cg (fun t => t ◇ (q70 ◇ q70)) (cg (fun t => ((q70 ◇ q70) ◇ q70) ◇ t) (apc133 q69 q70))))).trans (cg (fun t => ((((q70 ◇ q70) ◇ q70) ◇ ((q70 ◇ q70) ◇ q70)) ◇ (q70 ◇ q70)) ◇ t) (cg (fun t => (q70 ◇ q69) ◇ t) (cg (fun t => (((q70 ◇ q70) ◇ q70) ◇ ((q70 ◇ q70) ◇ q70)) ◇ t) (apc133 q69 q70))))).trans (cg (fun t => ((((q70 ◇ q70) ◇ q70) ◇ ((q70 ◇ q70) ◇ q70)) ◇ (q70 ◇ q70)) ◇ t) (cg (fun t => (q70 ◇ q69) ◇ t) (cg (fun t => t ◇ ((q70 ◇ q70) ◇ q70)) (apc99 q70 (((q70 ◇ q70) ◇ q70) ◇ ((q70 ◇ q70) ◇ q70))))))).trans (cg (fun t => t ◇ ((q70 ◇ q69) ◇ ((((q70 ◇ q70) ◇ q70) ◇ q70) ◇ ((q70 ◇ q70) ◇ q70)))) (cg (fun t => t ◇ (q70 ◇ q70)) (apc99 q70 (((q70 ◇ q70) ◇ q70) ◇ ((q70 ◇ q70) ◇ q70)))))).trans (cg (fun t => ((((q70 ◇ q70) ◇ q70) ◇ q70) ◇ (q70 ◇ q70)) ◇ t) (cg (fun t => (q70 ◇ q69) ◇ t) (apc4 q70 q70)))).trans (cg (fun t => t ◇ ((q70 ◇ q69) ◇ q70)) (apc19 q70 q70))).symm).trans (((cg (fun t => t ◇ ((q70 ◇ q69) ◇ ((((q70 ◇ q70) ◇ (q70 ◇ q69)) ◇ ((q70 ◇ q70) ◇ (q70 ◇ q69))) ◇ ((q70 ◇ q70) ◇ (q70 ◇ q69))))) (cg (fun t => t ◇ (q70 ◇ q70)) (cg (fun t => t ◇ ((q70 ◇ q70) ◇ (q70 ◇ q69))) (apc133 q69 q70)))).symm).trans (apc114 (q70 ◇ q70) (q70 ◇ q69)))
  have apc135:=fun (q71 q72:G)=>by
    exact ((apc133 (q71 ◇ q72) q72).symm).trans (((cg (fun t => t ◇ (q72 ◇ (q71 ◇ q72))) (apc134 q71 q72)).symm).trans (apc10 q71 q72 q72))
  have apc136:=fun (q73 q74:G)=>by
    exact (((((cg (fun t => t ◇ q73) (cg (fun t => t ◇ (q74 ◇ q74)) (cg (fun t => t ◇ (q74 ◇ q74)) (apc133 q74 q74)))).trans (cg (fun t => t ◇ q73) (cg (fun t => t ◇ (q74 ◇ q74)) (apc98 q74)))).trans (cg (fun t => t ◇ q73) (apc19 q74 q74))).symm).trans (((cg (fun t => t ◇ q73) (cg (fun t => t ◇ (q74 ◇ q74)) ((apc135 (((q73 ◇ q74) ◇ (q74 ◇ q74)) ◇ q73) (q74 ◇ q74)).symm))).symm).trans (apc42 q73 q74 (q74 ◇ q74)))).symm
  have apc139:=fun (q75 q76:G)=>by
    exact ((((cg (fun t => t ◇ q76) (cg (fun t => t ◇ ((q75 ◇ q75) ◇ q75)) (cg (fun t => t ◇ ((q75 ◇ q75) ◇ q75)) (apc99 q75 (((q75 ◇ q75) ◇ q75) ◇ ((q75 ◇ q75) ◇ q75)))))).trans (cg (fun t => t ◇ q76) (cg (fun t => t ◇ ((q75 ◇ q75) ◇ q75)) (apc4 q75 q75)))).trans (cg (fun t => t ◇ q76) (apc134 q75 q75))).symm).trans (((cg (fun t => t ◇ q76) (cg (fun t => t ◇ ((q75 ◇ q75) ◇ q75)) ((apc135 (((q76 ◇ (q75 ◇ q75)) ◇ (q75 ◇ q75)) ◇ q76) ((q75 ◇ q75) ◇ q75)).symm))).symm).trans (apc126 q75 q76 ((q75 ◇ q75) ◇ q75)))
  have apc143:=fun (q77 q78 q79:G)=>by
    exact ((apc139 q79 (q79 ◇ (q77 ◇ q78))).symm).trans (((cg (fun t => t ◇ (q79 ◇ (q77 ◇ q78))) ((apc136 ((q79 ◇ q77) ◇ q78) q79).symm)).symm).trans (apc10 q77 q78 q79))
  have apc149:=fun (q80 q81 q82 q83 q84:G)=>by
    exact (((apc143 q80 q81 q84).symm).trans (apc143 q82 q83 q84)).symm
  have apc198:=fun (q85 q86 q87 q88 q89:G)=>by
    exact ((apc149 q85 q86 q87 (q88 ◇ q89) ((q87 ◇ q88) ◇ q89)).symm).trans ((h q87 q88 q89).symm)
  exact (calc
    x=x:=rfl
    _=((((x ◇ y) ◇ y) ◇ (z ◇ x)) ◇ y):=(apc198 (z ◇ x) y x y y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_28506_to_36377 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_28506_to_36377
