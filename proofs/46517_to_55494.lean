-- Equation46517 → Equation55494
-- Recorded verdict: true
-- Premise: x * y = (z * y) * (y * (y * x))
-- Conclusion: x * (y * z) = w * ((z * u) * z)
-- Original submission SHA-256: 151f530657792a8e34c29830d41c03ba08289ef90d29da81c5f29cbd26c5c5d0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ y) ◇ (y ◇ (y ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = w ◇ ((z ◇ u) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc0:=fun (x y z:G)=>by
    exact ((h x y z).symm).trans (h x y x)
  have apc1:=fun (x y z:G)=>by
    exact ((h x y x).trans (apc0 x y x)).symm
  have apc2:=fun (q0 q1 q2 q3:G)=>by
    exact ((cg (fun t => (q3 ◇ (q2 ◇ q1)) ◇ t) (cg (fun t => (q2 ◇ q1) ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h (q1 ◇ (q1 ◇ q0)) (q2 ◇ q1) q3).symm)
  have apc3:=fun (q4 q5:G)=>by
    exact ((apc2 (q4 ◇ q5) q5 q4 q4).symm).trans ((h q5 (q4 ◇ q5) q4).symm)
  have apc4:=fun (q6:G)=>by
    exact (((cg (fun t => t ◇ (q6 ◇ (q6 ◇ q6))) (cg (fun t => (q6 ◇ q6) ◇ t) ((h q6 q6 q6).symm))).symm).trans (apc3 q6 (q6 ◇ q6))).trans (apc1 q6 q6 ((q6 ◇ q6) ◇ (q6 ◇ (q6 ◇ q6))))
  have apc5:=fun (q7 q8 q9:G)=>by
    exact ((cg (fun t => t ◇ ((q7 ◇ q8) ◇ ((q7 ◇ q8) ◇ q9))) (apc3 q7 q8)).symm).trans ((h q9 (q7 ◇ q8) (q8 ◇ (q8 ◇ (q7 ◇ q8)))).symm)
  have apc6:=fun (q0 q1 q10:G)=>by
    exact ((cg (fun t => t ◇ ((q1 ◇ (q1 ◇ q0)) ◇ ((q1 ◇ (q1 ◇ q0)) ◇ q10))) ((h q0 q1 q0).symm)).symm).trans ((h q10 (q1 ◇ (q1 ◇ q0)) (q0 ◇ q1)).symm)
  have apc10:=fun (q11 q12 q13 q14:G)=>by
    exact ((cg (fun t => (q14 ◇ (q13 ◇ (q12 ◇ q11))) ◇ t) (apc2 q12 q11 q12 q13)).symm).trans (apc2 (q12 ◇ q11) (q12 ◇ q11) q13 q14)
  have apc13:=fun (q15 q16:G)=>by
    exact (((cg (fun t => (q16 ◇ ((q15 ◇ q15) ◇ (q15 ◇ q15))) ◇ t) (apc4 q15)).symm).trans (apc2 q15 (q15 ◇ q15) (q15 ◇ q15) q16)).symm
  have apc14:=fun (q15 q16:G)=>by
    exact ((apc13 q15 q16).symm).trans (apc13 q15 q15)
  have apc15:=fun (q17:G)=>by
    exact ((cg (fun t => t ◇ (q17 ◇ q17)) (apc2 q17 q17 q17 q17)).symm).trans (apc14 q17 (q17 ◇ (q17 ◇ q17)))
  have apc16:=fun (q18 q19:G)=>by
    exact ((cg (fun t => ((q19 ◇ (q19 ◇ q18)) ◇ ((q19 ◇ (q19 ◇ q18)) ◇ (q18 ◇ q19))) ◇ t) (apc1 q18 q19 ((q18 ◇ q19) ◇ (q19 ◇ (q19 ◇ q18))))).symm).trans ((((cg (fun t => t ◇ ((q18 ◇ q19) ◇ (q19 ◇ (q19 ◇ q18)))) (cg (fun t => (q19 ◇ (q19 ◇ q18)) ◇ t) (cg (fun t => (q19 ◇ (q19 ◇ q18)) ◇ t) (apc1 q18 q19 q18)))).symm).trans (apc3 (q18 ◇ q19) (q19 ◇ (q19 ◇ q18)))).trans (cg (fun t => (q19 ◇ (q19 ◇ q18)) ◇ t) (apc1 q18 q19 ((q18 ◇ q19) ◇ (q19 ◇ (q19 ◇ q18))))))
  have apc17:=fun (q20:G)=>by
    exact ((((((((cg (fun t => t ◇ (((q20 ◇ q20) ◇ (q20 ◇ q20)) ◇ (q20 ◇ (q20 ◇ q20)))) (cg (fun t => ((q20 ◇ (q20 ◇ q20)) ◇ ((q20 ◇ (q20 ◇ q20)) ◇ ((q20 ◇ q20) ◇ (q20 ◇ q20)))) ◇ t) (cg (fun t => t ◇ (q20 ◇ q20)) (cg (fun t => (q20 ◇ (q20 ◇ q20)) ◇ t) (apc2 q20 q20 q20 q20))))).trans (cg (fun t => t ◇ (((q20 ◇ q20) ◇ (q20 ◇ q20)) ◇ (q20 ◇ (q20 ◇ q20)))) (cg (fun t => t ◇ (((q20 ◇ (q20 ◇ q20)) ◇ ((q20 ◇ (q20 ◇ q20)) ◇ (q20 ◇ q20))) ◇ (q20 ◇ q20))) (cg (fun t => (q20 ◇ (q20 ◇ q20)) ◇ t) (apc2 q20 q20 q20 q20))))).trans (cg (fun t => t ◇ (((q20 ◇ q20) ◇ (q20 ◇ q20)) ◇ (q20 ◇ (q20 ◇ q20)))) (cg (fun t => ((q20 ◇ (q20 ◇ q20)) ◇ ((q20 ◇ (q20 ◇ q20)) ◇ (q20 ◇ q20))) ◇ t) (apc16 q20 q20)))).trans (cg (fun t => (((q20 ◇ (q20 ◇ q20)) ◇ ((q20 ◇ (q20 ◇ q20)) ◇ (q20 ◇ q20))) ◇ ((q20 ◇ (q20 ◇ q20)) ◇ (q20 ◇ q20))) ◇ t) (apc4 q20))).trans (cg (fun t => t ◇ (q20 ◇ q20)) (apc10 q20 q20 (q20 ◇ (q20 ◇ q20)) (q20 ◇ (q20 ◇ q20))))).trans (cg (fun t => t ◇ (q20 ◇ q20)) (apc10 q20 q20 (q20 ◇ q20) (q20 ◇ q20)))).trans (apc14 q20 ((q20 ◇ q20) ◇ ((q20 ◇ q20) ◇ (q20 ◇ q20))))).symm).trans ((((cg (fun t => t ◇ (((q20 ◇ q20) ◇ (q20 ◇ q20)) ◇ (q20 ◇ (q20 ◇ q20)))) (cg (fun t => ((q20 ◇ (q20 ◇ q20)) ◇ ((q20 ◇ (q20 ◇ q20)) ◇ ((q20 ◇ q20) ◇ (q20 ◇ q20)))) ◇ t) (cg (fun t => ((q20 ◇ (q20 ◇ q20)) ◇ ((q20 ◇ (q20 ◇ q20)) ◇ ((q20 ◇ q20) ◇ (q20 ◇ q20)))) ◇ t) (apc4 q20)))).symm).trans (apc16 ((q20 ◇ q20) ◇ (q20 ◇ q20)) (q20 ◇ (q20 ◇ q20)))).trans (((cg (fun t => t ◇ (((q20 ◇ q20) ◇ (q20 ◇ q20)) ◇ (q20 ◇ (q20 ◇ q20)))) (cg (fun t => (q20 ◇ (q20 ◇ q20)) ◇ t) (apc2 q20 q20 q20 q20))).trans (cg (fun t => ((q20 ◇ (q20 ◇ q20)) ◇ ((q20 ◇ (q20 ◇ q20)) ◇ (q20 ◇ q20))) ◇ t) (apc4 q20))).trans (apc16 q20 q20)))
  have apc19:=fun (q17 q20:G)=>by
    exact (apc15 q17).trans (apc17 q17)
  have apc20:=fun (q21 q22 q23 q24:G)=>by
    exact ((cg (fun t => (q24 ◇ (q21 ◇ q22)) ◇ t) (cg (fun t => t ◇ (q23 ◇ (q22 ◇ (q22 ◇ q21)))) (apc1 q21 q22 ((q21 ◇ q22) ◇ (q22 ◇ (q22 ◇ q21)))))).symm).trans ((((cg (fun t => t ◇ (((q21 ◇ q22) ◇ (q22 ◇ (q22 ◇ q21))) ◇ (q23 ◇ (q22 ◇ (q22 ◇ q21))))) (cg (fun t => q24 ◇ t) (apc1 q21 q22 q21))).symm).trans (apc2 q23 (q22 ◇ (q22 ◇ q21)) (q21 ◇ q22) q24)).trans (cg (fun t => ((q22 ◇ (q22 ◇ q21)) ◇ ((q22 ◇ (q22 ◇ q21)) ◇ q23)) ◇ t) (apc1 q21 q22 ((q21 ◇ q22) ◇ (q22 ◇ (q22 ◇ q21))))))
  have apc21:=fun (q25 q26 q27:G)=>by
    exact (((cg (fun t => (q27 ◇ (q25 ◇ q26)) ◇ t) ((h (q26 ◇ q25) q26 q25).symm)).symm).trans (apc20 q25 q26 q26 q27)).symm
  have apc22:=fun (q25 q26 q27:G)=>by
    exact ((apc21 q25 q26 q27).symm).trans (apc21 q25 q26 q25)
  have apc25:=fun (q28:G)=>by
    exact (((apc19 q28 (((q28 ◇ (q28 ◇ q28)) ◇ (q28 ◇ q28)) ◇ (q28 ◇ q28))).symm).trans (((cg (fun t => t ◇ (q28 ◇ q28)) (apc2 q28 q28 q28 q28)).symm).trans ((apc13 q28 (q28 ◇ (q28 ◇ q28))).symm))).symm
  have apc26:=fun (q29 q30:G)=>by
    exact (((((cg (fun t => t ◇ (((q29 ◇ (q29 ◇ q29)) ◇ (q29 ◇ q29)) ◇ ((q29 ◇ q29) ◇ ((q29 ◇ q29) ◇ q29)))) (cg (fun t => q30 ◇ t) (apc2 (q29 ◇ q29) q29 q29 (q29 ◇ q29)))).trans (cg (fun t => t ◇ (((q29 ◇ (q29 ◇ q29)) ◇ (q29 ◇ q29)) ◇ ((q29 ◇ q29) ◇ ((q29 ◇ q29) ◇ q29)))) (cg (fun t => q30 ◇ t) (apc3 q29 q29)))).trans (cg (fun t => (q30 ◇ (q29 ◇ (q29 ◇ q29))) ◇ t) (apc2 (q29 ◇ q29) q29 q29 (q29 ◇ (q29 ◇ q29))))).trans (cg (fun t => (q30 ◇ (q29 ◇ (q29 ◇ q29))) ◇ t) (apc3 q29 q29))).symm).trans ((((cg (fun t => (q30 ◇ (((q29 ◇ q29) ◇ (q29 ◇ q29)) ◇ ((q29 ◇ q29) ◇ ((q29 ◇ q29) ◇ q29)))) ◇ t) (cg (fun t => t ◇ ((q29 ◇ q29) ◇ ((q29 ◇ q29) ◇ q29))) (apc25 q29))).symm).trans (apc22 ((q29 ◇ q29) ◇ (q29 ◇ q29)) ((q29 ◇ q29) ◇ ((q29 ◇ q29) ◇ q29)) q30)).trans (((((((cg (fun t => (((q29 ◇ q29) ◇ (q29 ◇ q29)) ◇ (((q29 ◇ q29) ◇ (q29 ◇ q29)) ◇ ((q29 ◇ q29) ◇ ((q29 ◇ q29) ◇ q29)))) ◇ t) (cg (fun t => t ◇ ((q29 ◇ q29) ◇ ((q29 ◇ q29) ◇ q29))) (apc25 q29))).trans (cg (fun t => t ◇ (((q29 ◇ (q29 ◇ q29)) ◇ (q29 ◇ q29)) ◇ ((q29 ◇ q29) ◇ ((q29 ◇ q29) ◇ q29)))) (cg (fun t => ((q29 ◇ q29) ◇ (q29 ◇ q29)) ◇ t) (apc2 (q29 ◇ q29) q29 q29 (q29 ◇ q29))))).trans (cg (fun t => t ◇ (((q29 ◇ (q29 ◇ q29)) ◇ (q29 ◇ q29)) ◇ ((q29 ◇ q29) ◇ ((q29 ◇ q29) ◇ q29)))) (cg (fun t => ((q29 ◇ q29) ◇ (q29 ◇ q29)) ◇ t) (apc3 q29 q29)))).trans (cg (fun t => t ◇ (((q29 ◇ (q29 ◇ q29)) ◇ (q29 ◇ q29)) ◇ ((q29 ◇ q29) ◇ ((q29 ◇ q29) ◇ q29)))) (apc4 q29))).trans (cg (fun t => (q29 ◇ q29) ◇ t) (apc2 (q29 ◇ q29) q29 q29 (q29 ◇ (q29 ◇ q29))))).trans (cg (fun t => (q29 ◇ q29) ◇ t) (apc3 q29 q29))).trans (apc1 q29 q29 ((q29 ◇ q29) ◇ (q29 ◇ (q29 ◇ q29))))))
  have apc27:=fun (q31:G)=>by
    exact ((cg (fun t => ((q31 ◇ q31) ◇ q31) ◇ t) (apc3 q31 q31)).symm).trans (((cg (fun t => ((q31 ◇ q31) ◇ q31) ◇ t) (cg (fun t => (q31 ◇ (q31 ◇ (q31 ◇ q31))) ◇ t) (apc26 q31 q31))).symm).trans (apc6 (q31 ◇ q31) q31 (q31 ◇ (q31 ◇ q31))))
  have apc28:=fun (q32:G)=>by
    exact ((apc27 q32).symm).trans ((h q32 q32 (q32 ◇ q32)).symm)
  have apc29:=fun (q33:G)=>by
    exact ((((cg (fun t => t ◇ ((q33 ◇ (q33 ◇ q33)) ◇ (q33 ◇ (q33 ◇ (q33 ◇ q33))))) (cg (fun t => (q33 ◇ (q33 ◇ (q33 ◇ q33))) ◇ t) (apc3 q33 q33))).trans (cg (fun t => t ◇ ((q33 ◇ (q33 ◇ q33)) ◇ (q33 ◇ (q33 ◇ (q33 ◇ q33))))) (apc26 q33 q33))).trans (cg (fun t => (q33 ◇ q33) ◇ t) (apc28 q33))).symm).trans ((((cg (fun t => t ◇ ((q33 ◇ (q33 ◇ q33)) ◇ (q33 ◇ (q33 ◇ (q33 ◇ q33))))) (cg (fun t => (q33 ◇ (q33 ◇ (q33 ◇ q33))) ◇ t) (cg (fun t => (q33 ◇ (q33 ◇ (q33 ◇ q33))) ◇ t) (apc28 q33)))).symm).trans (apc3 (q33 ◇ (q33 ◇ q33)) (q33 ◇ (q33 ◇ (q33 ◇ q33))))).trans ((cg (fun t => (q33 ◇ (q33 ◇ (q33 ◇ q33))) ◇ t) (apc28 q33)).trans (apc3 q33 q33)))
  have apc30:=fun (q34:G)=>by
    exact (((((((cg (fun t => ((q34 ◇ q34) ◇ (q34 ◇ (q34 ◇ q34))) ◇ t) (cg (fun t => (q34 ◇ q34) ◇ t) (cg (fun t => (q34 ◇ q34) ◇ t) (apc29 q34)))).trans (cg (fun t => ((q34 ◇ q34) ◇ (q34 ◇ (q34 ◇ q34))) ◇ t) (cg (fun t => (q34 ◇ q34) ◇ t) (apc1 q34 q34 ((q34 ◇ q34) ◇ (q34 ◇ (q34 ◇ q34))))))).trans (cg (fun t => ((q34 ◇ q34) ◇ (q34 ◇ (q34 ◇ q34))) ◇ t) (apc29 q34))).trans (cg (fun t => t ◇ (q34 ◇ (q34 ◇ q34))) (apc1 q34 q34 ((q34 ◇ q34) ◇ (q34 ◇ (q34 ◇ q34)))))).trans (apc1 q34 q34 ((q34 ◇ q34) ◇ (q34 ◇ (q34 ◇ q34))))).symm).trans ((((cg (fun t => t ◇ ((q34 ◇ q34) ◇ ((q34 ◇ q34) ◇ ((q34 ◇ q34) ◇ (q34 ◇ q34))))) (cg (fun t => (q34 ◇ q34) ◇ t) (apc29 q34))).symm).trans (apc28 (q34 ◇ q34))).trans (apc29 q34))).symm
  have apc32:=fun (q35 q36:G)=>by
    exact ((cg (fun t => (q36 ◇ q35) ◇ t) (apc30 q35)).symm).trans ((h q35 q35 q36).symm)
  have apc33:=fun (q37:G)=>by
    exact ((((cg (fun t => (q37 ◇ q37) ◇ t) (apc30 q37)).trans (apc32 q37 q37)).symm).trans (((cg (fun t => (q37 ◇ q37) ◇ t) (cg (fun t => q37 ◇ t) (apc30 q37))).symm).trans ((h (q37 ◇ q37) q37 q37).symm))).symm
  have apc35:=fun (q38 q39:G)=>by
    exact ((cg (fun t => t ◇ (q39 ◇ (q39 ◇ q38))) (apc33 q39)).symm).trans ((h q38 q39 (q39 ◇ q39)).symm)
  have apc37:=fun (q40 q41 q42:G)=>by
    exact ((cg (fun t => (q42 ◇ (q41 ◇ q40)) ◇ t) (apc32 q40 q41)).symm).trans (((cg (fun t => (q42 ◇ (q41 ◇ q40)) ◇ t) (cg (fun t => (q41 ◇ q40) ◇ t) (apc32 q40 q41))).symm).trans ((h (q40 ◇ q40) (q41 ◇ q40) q42).symm))
  have apc38:=fun (q43 q44:G)=>by
    exact (((cg (fun t => ((q43 ◇ q43) ◇ (q44 ◇ q43)) ◇ t) (apc32 q43 q43)).trans (apc37 q43 q44 (q43 ◇ q43))).symm).trans ((((cg (fun t => t ◇ ((q43 ◇ q43) ◇ (q43 ◇ q43))) (apc37 q43 q44 q43)).symm).trans (apc32 (q43 ◇ q43) (q43 ◇ (q44 ◇ q43)))).trans (apc32 q43 q43))
  have apc39:=fun (q45 q46:G)=>by
    exact ((cg (fun t => (q46 ◇ (q45 ◇ q46)) ◇ t) (apc32 q46 q45)).symm).trans ((((cg (fun t => (q46 ◇ (q45 ◇ q46)) ◇ t) (cg (fun t => (q45 ◇ q46) ◇ t) (apc32 q46 q45))).symm).trans (apc5 q45 q46 (q46 ◇ q46))).trans (apc38 q46 q45))
  have apc40:=fun (q47 q48:G)=>by
    exact ((((cg (fun t => (q48 ◇ q48) ◇ t) (apc38 q48 q47)).trans (apc32 q48 q48)).symm).trans (((cg (fun t => t ◇ ((q48 ◇ q48) ◇ (q47 ◇ q48))) (apc39 q47 q48)).symm).trans (apc2 q47 q48 q48 (q48 ◇ (q47 ◇ q48))))).symm
  have apc41:=fun (q49 q50:G)=>by
    exact ((((cg (fun t => ((q50 ◇ q50) ◇ (q50 ◇ (q50 ◇ q49))) ◇ t) (apc40 q49 q50)).trans (cg (fun t => t ◇ (q50 ◇ q50)) (apc35 q49 q50))).trans (apc32 q50 q49)).symm).trans ((((cg (fun t => ((q50 ◇ q50) ◇ (q50 ◇ (q50 ◇ q49))) ◇ t) (cg (fun t => (q50 ◇ (q50 ◇ q49)) ◇ t) (apc40 q49 q50))).symm).trans (apc1 (q50 ◇ q50) (q50 ◇ (q50 ◇ q49)) q49)).trans (apc35 q49 q50))
  have apc42:=fun (q51 q52 q53:G)=>by
    exact (((apc41 q51 q53).symm).trans (apc41 q52 q53)).symm
  have apc46:=fun (q54 q55 q56:G)=>by
    exact ((apc42 q54 (q55 ◇ q55) (q56 ◇ q55)).symm).trans (apc38 q55 q56)
  have apc47:=fun (x y z q54 q55 q56:G)=>by
    exact (h x y x).trans ((cg (fun t => (x ◇ y) ◇ t) (apc46 y x y)).trans (apc46 (x ◇ y) x x))
  have apc57:=fun (q57 q58:G)=>by
    exact (((cg (fun t => t ◇ (q57 ◇ q58)) (apc47 q57 q58 (q57 ◇ q58) (q57 ◇ q58) (q57 ◇ q58) (q57 ◇ q58))).trans (cg (fun t => (q57 ◇ q57) ◇ t) (apc47 q57 q58 (q57 ◇ q58) (q57 ◇ q58) (q57 ◇ q58) (q57 ◇ q58)))).symm).trans (((apc41 (q58 ◇ (q58 ◇ (q57 ◇ q58))) (q57 ◇ q58)).trans (apc3 q57 q58)).trans ((cg (fun t => q58 ◇ t) (apc47 q57 q58 (q57 ◇ q58) (q57 ◇ q58) (q57 ◇ q58) (q57 ◇ q58))).trans (apc47 q58 (q57 ◇ q57) (q58 ◇ (q57 ◇ q57)) (q58 ◇ (q57 ◇ q57)) (q58 ◇ (q57 ◇ q57)) (q58 ◇ (q57 ◇ q57)))))
  exact (calc
    (x ◇ (y ◇ z))=(x ◇ x):=apc47 x (y ◇ z) u u u u
    _=((u ◇ u) ◇ (u ◇ u)):=(apc57 u x).symm
    _=(w ◇ w):=((apc57 u w).symm).symm
    _=(w ◇ ((z ◇ u) ◇ z)):=(apc47 w ((z ◇ u) ◇ z) u u u u).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46517_to_55494 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46517_to_55494
