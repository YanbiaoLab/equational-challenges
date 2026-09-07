-- Equation47151 → Equation58633
-- Recorded verdict: true
-- Premise: x * y = (y * x) * ((x * z) * x)
-- Conclusion: (x * y) * y = z * (x * (w * y))
-- Original submission SHA-256: 373becf0e22a0f0f90cd2a89944c511c67af22d6038d0af1d5fe624cb6e8cf62
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ x) ◇ ((x ◇ z) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ y = z ◇ (x ◇ (w ◇ y))
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
    exact ((h x y z).symm).trans (h x y x)
  have apc1:=fun (x y z:G)=>by
    exact ((h x y x).trans (apc0 x y x)).symm
  have apc2:=fun (q0 q1 q2:G)=>by
    exact ((cg (fun t => (q2 ◇ (q1 ◇ q0)) ◇ t) (cg (fun t => t ◇ (q1 ◇ q0)) ((h q0 q1 q0).symm))).symm).trans ((h (q1 ◇ q0) q2 ((q0 ◇ q0) ◇ q0)).symm)
  have apc3:=fun (q3 q2 q4:G)=>by
    exact ((cg (fun t => (q2 ◇ ((q4 ◇ q3) ◇ q4)) ◇ t) ((h q4 ((q4 ◇ q3) ◇ q4) q3).symm)).symm).trans ((h ((q4 ◇ q3) ◇ q4) q2 q4).symm)
  have apc4:=fun (q5 q6 q7:G)=>by
    exact ((cg (fun t => t ◇ (q7 ◇ ((q7 ◇ q6) ◇ q7))) ((h q7 q5 q6).symm)).symm).trans (apc3 q6 (q5 ◇ q7) q7)
  have apc5:=fun (q8 q9:G)=>by
    exact ((apc4 ((q9 ◇ q8) ◇ q9) q8 q9).symm).trans (apc3 q8 q9 q9)
  have apc6:=fun (q10 q11 q12:G)=>by
    exact ((cg (fun t => t ◇ ((q12 ◇ (q12 ◇ q11)) ◇ ((q12 ◇ q11) ◇ q12))) ((h q12 q10 q11).symm)).symm).trans (apc2 q12 (q12 ◇ q11) (q10 ◇ q12))
  have apc8:=fun (q13 q14:G)=>by
    exact ((cg (fun t => (q14 ◇ ((q13 ◇ q13) ◇ (q13 ◇ q13))) ◇ t) (apc2 q13 q13 (q13 ◇ q13))).symm).trans (apc2 (q13 ◇ q13) (q13 ◇ q13) q14)
  have apc9:=fun (q15 q16:G)=>by
    exact ((cg (fun t => t ◇ ((q16 ◇ q16) ◇ (q16 ◇ q16))) (apc2 q16 q16 q15)).symm).trans (apc8 q16 (q15 ◇ (q16 ◇ q16)))
  have apc10:=fun (q17:G)=>by
    exact (((apc1 (q17 ◇ q17) (q17 ◇ q17) (((q17 ◇ q17) ◇ (q17 ◇ q17)) ◇ (((q17 ◇ q17) ◇ (q17 ◇ q17)) ◇ (q17 ◇ q17)))).symm).trans (((apc9 ((q17 ◇ q17) ◇ (q17 ◇ q17)) q17).symm).trans (apc8 q17 (q17 ◇ q17)))).symm
  have apc11:=fun (q18:G)=>by
    exact ((((cg (fun t => ((q18 ◇ q18) ◇ (q18 ◇ q18)) ◇ t) (apc10 q18)).trans (apc2 q18 q18 (q18 ◇ q18))).symm).trans (((cg (fun t => t ◇ (((q18 ◇ q18) ◇ (q18 ◇ q18)) ◇ (q18 ◇ q18))) (apc10 q18)).symm).trans (apc1 (q18 ◇ q18) ((q18 ◇ q18) ◇ (q18 ◇ q18)) q18))).symm
  have apc12:=fun (q19 q20:G)=>by
    exact ((((cg (fun t => t ◇ (((q19 ◇ q20) ◇ (q20 ◇ q19)) ◇ ((q19 ◇ q20) ◇ (q20 ◇ q19)))) (cg (fun t => ((q20 ◇ q19) ◇ (q19 ◇ q20)) ◇ t) (apc2 q19 q20 (q19 ◇ q20)))).trans (cg (fun t => (((q20 ◇ q19) ◇ (q19 ◇ q20)) ◇ ((q20 ◇ q19) ◇ (q19 ◇ q20))) ◇ t) (apc2 q19 q20 (q19 ◇ q20)))).trans (cg (fun t => t ◇ ((q20 ◇ q19) ◇ (q19 ◇ q20))) (apc2 q20 q19 (q20 ◇ q19)))).symm).trans ((((cg (fun t => t ◇ (((q19 ◇ q20) ◇ (q20 ◇ q19)) ◇ ((q19 ◇ q20) ◇ (q20 ◇ q19)))) (cg (fun t => t ◇ (((q19 ◇ q20) ◇ (q20 ◇ q19)) ◇ ((q19 ◇ q20) ◇ (q20 ◇ q19)))) (apc2 q19 q20 (q19 ◇ q20)))).symm).trans (apc10 ((q19 ◇ q20) ◇ (q20 ◇ q19)))).trans (((cg (fun t => t ◇ (((q19 ◇ q20) ◇ (q20 ◇ q19)) ◇ ((q19 ◇ q20) ◇ (q20 ◇ q19)))) (apc2 q19 q20 (q19 ◇ q20))).trans (cg (fun t => ((q20 ◇ q19) ◇ (q19 ◇ q20)) ◇ t) (apc2 q19 q20 (q19 ◇ q20)))).trans (apc2 q20 q19 (q20 ◇ q19))))
  have apc13:=fun (q21 q22:G)=>by
    exact (((((((cg (fun t => (((q21 ◇ q22) ◇ (q22 ◇ q21)) ◇ ((q21 ◇ q22) ◇ (q22 ◇ q21))) ◇ t) (cg (fun t => t ◇ ((q21 ◇ q22) ◇ (q22 ◇ q21))) (cg (fun t => t ◇ ((q21 ◇ q22) ◇ (q22 ◇ q21))) (apc12 q21 q22)))).trans (cg (fun t => (((q21 ◇ q22) ◇ (q22 ◇ q21)) ◇ ((q21 ◇ q22) ◇ (q22 ◇ q21))) ◇ t) (cg (fun t => t ◇ ((q21 ◇ q22) ◇ (q22 ◇ q21))) (apc2 q21 q22 (q21 ◇ q22))))).trans (cg (fun t => t ◇ (((q22 ◇ q21) ◇ (q21 ◇ q22)) ◇ ((q21 ◇ q22) ◇ (q22 ◇ q21)))) (apc2 q21 q22 (q21 ◇ q22)))).trans (cg (fun t => ((q22 ◇ q21) ◇ (q21 ◇ q22)) ◇ t) (apc12 q22 q21))).trans (apc2 q22 q21 (q22 ◇ q21))).symm).trans ((((cg (fun t => t ◇ (((((q21 ◇ q22) ◇ (q22 ◇ q21)) ◇ ((q22 ◇ q21) ◇ (q21 ◇ q22))) ◇ ((q21 ◇ q22) ◇ (q22 ◇ q21))) ◇ ((q21 ◇ q22) ◇ (q22 ◇ q21)))) (cg (fun t => t ◇ ((q21 ◇ q22) ◇ (q22 ◇ q21))) (apc12 q21 q22))).symm).trans (apc5 ((q22 ◇ q21) ◇ (q21 ◇ q22)) ((q21 ◇ q22) ◇ (q22 ◇ q21)))).trans (((cg (fun t => t ◇ ((q21 ◇ q22) ◇ (q22 ◇ q21))) (cg (fun t => t ◇ ((q21 ◇ q22) ◇ (q22 ◇ q21))) (apc12 q21 q22))).trans (cg (fun t => t ◇ ((q21 ◇ q22) ◇ (q22 ◇ q21))) (apc2 q21 q22 (q21 ◇ q22)))).trans (apc12 q22 q21)))).symm
  have apc15:=fun (q23 q24 q25:G)=>by
    exact ((((((((((((cg (fun t => t ◇ ((((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))) ◇ (((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))))) (cg (fun t => q25 ◇ t) (cg (fun t => t ◇ (((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23)))) (apc13 q23 q24)))).trans (cg (fun t => t ◇ ((((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))) ◇ (((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))))) (cg (fun t => q25 ◇ t) (cg (fun t => ((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ t) (apc2 q23 q24 (q23 ◇ q24)))))).trans (cg (fun t => t ◇ ((((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))) ◇ (((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))))) (cg (fun t => q25 ◇ t) (cg (fun t => ((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ t) (apc13 q23 q24))))).trans (cg (fun t => t ◇ ((((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))) ◇ (((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))))) (cg (fun t => q25 ◇ t) (apc2 q23 q24 (q23 ◇ q24))))).trans (cg (fun t => t ◇ ((((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))) ◇ (((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))))) (cg (fun t => q25 ◇ t) (apc13 q23 q24)))).trans (cg (fun t => (q25 ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))) ◇ t) (cg (fun t => t ◇ (((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23)))) (apc2 q23 q24 (q23 ◇ q24))))).trans (cg (fun t => (q25 ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))) ◇ t) (cg (fun t => t ◇ (((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23)))) (apc13 q23 q24)))).trans (cg (fun t => (q25 ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))) ◇ t) (cg (fun t => ((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ t) (apc2 q23 q24 (q23 ◇ q24))))).trans (cg (fun t => (q25 ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))) ◇ t) (cg (fun t => ((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ t) (apc13 q23 q24)))).trans (cg (fun t => (q25 ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))) ◇ t) (apc2 q23 q24 (q23 ◇ q24)))).trans (cg (fun t => (q25 ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))) ◇ t) (apc13 q23 q24))).symm).trans ((((cg (fun t => t ◇ ((((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))) ◇ (((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))))) (cg (fun t => q25 ◇ t) (cg (fun t => t ◇ (((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23)))) (apc2 q23 q24 (q23 ◇ q24))))).symm).trans (apc8 ((q23 ◇ q24) ◇ (q24 ◇ q23)) q25)).trans ((((((cg (fun t => t ◇ q25) (cg (fun t => t ◇ (((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23)))) (apc2 q23 q24 (q23 ◇ q24)))).trans (cg (fun t => t ◇ q25) (cg (fun t => t ◇ (((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23)))) (apc13 q23 q24)))).trans (cg (fun t => t ◇ q25) (cg (fun t => ((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ t) (apc2 q23 q24 (q23 ◇ q24))))).trans (cg (fun t => t ◇ q25) (cg (fun t => ((q23 ◇ q24) ◇ (q24 ◇ q23)) ◇ t) (apc13 q23 q24)))).trans (cg (fun t => t ◇ q25) (apc2 q23 q24 (q23 ◇ q24)))).trans (cg (fun t => t ◇ q25) (apc13 q23 q24))))
  have apc16:=fun (q26 q27 q28:G)=>by
    exact ((cg (fun t => t ◇ ((q27 ◇ q28) ◇ (q28 ◇ q27))) (apc2 q27 q28 q26)).symm).trans (apc15 q27 q28 (q26 ◇ (q28 ◇ q27)))
  have apc17:=fun (q29 q30:G)=>by
    exact ((apc16 (q30 ◇ q29) q29 q30).symm).trans (apc2 q29 q30 (q30 ◇ q29))
  have apc18:=fun (q31 q32:G)=>by
    exact (((cg (fun t => ((q32 ◇ q31) ◇ (q32 ◇ q31)) ◇ t) (apc10 (q32 ◇ q31))).trans (apc11 (q32 ◇ q31))).symm).trans ((((cg (fun t => t ◇ ((((q32 ◇ q31) ◇ (q32 ◇ q31)) ◇ ((q32 ◇ q31) ◇ (q32 ◇ q31))) ◇ ((q32 ◇ q31) ◇ (q32 ◇ q31)))) (apc17 q31 q32)).symm).trans (apc1 ((q32 ◇ q31) ◇ (q32 ◇ q31)) ((q31 ◇ q32) ◇ (q32 ◇ q31)) q31)).trans (apc2 q31 q32 (q32 ◇ q31)))
  have apc19:=fun (q33:G)=>by
    exact ((cg (fun t => (q33 ◇ (q33 ◇ q33)) ◇ t) (apc1 q33 (q33 ◇ q33) (((q33 ◇ q33) ◇ q33) ◇ ((q33 ◇ q33) ◇ q33)))).symm).trans ((((cg (fun t => t ◇ (((q33 ◇ q33) ◇ q33) ◇ ((q33 ◇ q33) ◇ q33))) (apc1 q33 (q33 ◇ q33) q33)).symm).trans (apc18 q33 (q33 ◇ q33))).trans (apc1 q33 (q33 ◇ q33) (((q33 ◇ q33) ◇ q33) ◇ ((q33 ◇ q33) ◇ q33))))
  have apc22:=fun (q34 q35:G)=>by
    exact (((cg (fun t => ((q34 ◇ (q34 ◇ q34)) ◇ q35) ◇ t) (cg (fun t => (q34 ◇ (q34 ◇ q34)) ◇ t) (apc19 q34))).trans (cg (fun t => ((q34 ◇ (q34 ◇ q34)) ◇ q35) ◇ t) (apc19 q34))).symm).trans ((((cg (fun t => ((q34 ◇ (q34 ◇ q34)) ◇ q35) ◇ t) (cg (fun t => (q34 ◇ (q34 ◇ q34)) ◇ t) (cg (fun t => t ◇ (q34 ◇ (q34 ◇ q34))) (apc19 q34)))).symm).trans (apc4 q35 (q34 ◇ (q34 ◇ q34)) (q34 ◇ (q34 ◇ q34)))).trans ((cg (fun t => t ◇ (q35 ◇ (q34 ◇ (q34 ◇ q34)))) (cg (fun t => t ◇ (q34 ◇ (q34 ◇ q34))) (apc19 q34))).trans (cg (fun t => t ◇ (q35 ◇ (q34 ◇ (q34 ◇ q34)))) (apc19 q34))))
  have apc23:=fun (q10 q11 q12 q21 q22:G)=>by
    exact ((cg (fun t => (q12 ◇ q10) ◇ t) (apc13 (q12 ◇ q11) q12)).symm).trans (apc6 q10 q11 q12)
  have apc24:=fun (q36 q37:G)=>by
    exact ((apc23 (q37 ◇ (q37 ◇ q36)) q36 q37 q36 q36).symm).trans (apc2 (q37 ◇ q36) q37 q37)
  have apc25:=fun (q38:G)=>by
    exact ((((apc2 q38 q38 ((q38 ◇ q38) ◇ q38)).trans (apc1 q38 q38 ((q38 ◇ q38) ◇ ((q38 ◇ q38) ◇ q38)))).symm).trans ((((cg (fun t => (((q38 ◇ q38) ◇ q38) ◇ (q38 ◇ q38)) ◇ t) (cg (fun t => t ◇ (q38 ◇ q38)) ((h q38 q38 q38).symm))).symm).trans (apc24 q38 (q38 ◇ q38))).trans (cg (fun t => t ◇ (q38 ◇ q38)) (apc1 q38 q38 ((q38 ◇ q38) ◇ ((q38 ◇ q38) ◇ q38)))))).symm
  have apc26:=fun (q39 q40:G)=>by
    exact ((apc24 q39 q40).symm).trans ((h q40 (q40 ◇ q39) (q40 ◇ q39)).symm)
  have apc27:=fun (q41:G)=>by
    exact ((((cg (fun t => (q41 ◇ ((q41 ◇ q41) ◇ q41)) ◇ t) (cg (fun t => t ◇ ((q41 ◇ q41) ◇ q41)) (apc5 q41 q41))).trans (cg (fun t => (q41 ◇ ((q41 ◇ q41) ◇ q41)) ◇ t) (apc1 q41 ((q41 ◇ q41) ◇ q41) ((((q41 ◇ q41) ◇ q41) ◇ q41) ◇ ((q41 ◇ q41) ◇ q41))))).trans (apc3 q41 q41 q41)).symm).trans ((((cg (fun t => t ◇ ((((q41 ◇ q41) ◇ q41) ◇ (((q41 ◇ q41) ◇ q41) ◇ q41)) ◇ ((q41 ◇ q41) ◇ q41))) (apc1 q41 ((q41 ◇ q41) ◇ q41) q41)).symm).trans (apc24 q41 ((q41 ◇ q41) ◇ q41))).trans ((cg (fun t => t ◇ ((q41 ◇ q41) ◇ q41)) (apc5 q41 q41)).trans (apc1 q41 ((q41 ◇ q41) ◇ q41) ((((q41 ◇ q41) ◇ q41) ◇ q41) ◇ ((q41 ◇ q41) ◇ q41)))))
  have apc28:=fun (q42 q43 q44:G)=>by
    exact ((cg (fun t => (q44 ◇ q43) ◇ t) (apc26 q42 q43)).symm).trans ((h q43 q44 (q43 ◇ q42)).symm)
  have apc29:=fun (q45 q46:G)=>by
    exact ((cg (fun t => (q46 ◇ (q45 ◇ q45)) ◇ t) (apc25 q45)).symm).trans (((cg (fun t => (q46 ◇ (q45 ◇ q45)) ◇ t) (cg (fun t => t ◇ (q45 ◇ q45)) (apc25 q45))).symm).trans ((h (q45 ◇ q45) q46 (q45 ◇ q45)).symm))
  have apc30:=fun (q47:G)=>by
    exact (((apc28 q47 q47 (q47 ◇ q47)).symm).trans ((((cg (fun t => t ◇ (q47 ◇ (q47 ◇ q47))) (apc29 q47 q47)).symm).trans (apc22 q47 (q47 ◇ q47))).trans ((cg (fun t => (q47 ◇ (q47 ◇ q47)) ◇ t) (apc28 q47 q47 q47)).trans (apc29 q47 q47)))).symm
  have apc31:=fun (q48:G)=>by
    exact (((cg (fun t => (q48 ◇ (q48 ◇ q48)) ◇ t) (apc25 q48)).trans (apc29 q48 q48)).symm).trans ((((cg (fun t => t ◇ ((q48 ◇ q48) ◇ (q48 ◇ q48))) (apc30 q48)).symm).trans (apc16 q48 q48 q48)).trans ((cg (fun t => t ◇ (q48 ◇ (q48 ◇ q48))) (apc25 q48)).trans (apc28 q48 q48 q48)))
  have apc32:=fun (q41 q48:G)=>by
    exact ((((cg (fun t => t ◇ q41) (apc31 q41)).trans (apc31 q41)).symm).trans ((apc27 q41).trans (cg (fun t => q41 ◇ t) (apc31 q41)))).symm
  have apc33:=fun (x y z q48:G)=>by
    exact ((cg (fun t => (y ◇ x) ◇ t) (apc31 x)).symm).trans (apc1 x y x)
  have apc34:=fun (q49 q50:G)=>by
    exact ((((cg (fun t => (q50 ◇ q49) ◇ t) (cg (fun t => q50 ◇ t) (apc31 q50))).trans (cg (fun t => (q50 ◇ q49) ◇ t) (apc32 q50 (q50 ◇ (q50 ◇ q50))))).symm).trans ((((cg (fun t => (q50 ◇ q49) ◇ t) (cg (fun t => q50 ◇ t) (cg (fun t => t ◇ q50) (apc32 q50 q49)))).symm).trans (apc4 q49 (q50 ◇ q50) q50)).trans ((cg (fun t => t ◇ (q49 ◇ q50)) (cg (fun t => t ◇ q50) (apc32 q50 (q50 ◇ (q50 ◇ q50))))).trans (cg (fun t => t ◇ (q49 ◇ q50)) (apc31 q50))))).symm
  have apc35:=fun (x y z q29 q30 q48:G)=>by
    exact (((apc13 q29 q30).symm).trans (((apc33 (q30 ◇ q29) (q29 ◇ q30) (((q29 ◇ q30) ◇ (q30 ◇ q29)) ◇ ((q30 ◇ q29) ◇ (q30 ◇ q29))) (((q29 ◇ q30) ◇ (q30 ◇ q29)) ◇ ((q30 ◇ q29) ◇ (q30 ◇ q29)))).symm).trans (apc17 q29 q30))).symm
  have apc37:=fun (q10 q11 q12 q21 q22 q42 q43 q44:G)=>by
    exact ((cg (fun t => (q12 ◇ q10) ◇ t) (apc28 q11 q12 (q12 ◇ q11))).symm).trans (apc23 q10 q11 q12 q10 q10)
  have apc38:=fun (q51 q52:G)=>by
    exact (((apc28 q51 q52 q52).symm).trans ((((cg (fun t => t ◇ (q52 ◇ (q52 ◇ q51))) (apc32 q52 q51)).symm).trans (apc37 (q52 ◇ q52) q51 q52 q51 q51 q51 q51 q51)).trans ((cg (fun t => ((q52 ◇ q51) ◇ q52) ◇ t) (apc31 q52)).trans (apc33 q52 (q52 ◇ q51) (((q52 ◇ q51) ◇ q52) ◇ (q52 ◇ q52)) (((q52 ◇ q51) ◇ q52) ◇ (q52 ◇ q52)))))).symm
  have apc39:=fun (q53 q54:G)=>by
    exact ((cg (fun t => t ◇ (q54 ◇ q53)) (apc13 q53 q54)).symm).trans ((((cg (fun t => t ◇ (q54 ◇ q53)) (cg (fun t => (q54 ◇ q53) ◇ t) (apc1 q53 q54 q53))).symm).trans (apc26 ((q53 ◇ q53) ◇ q53) (q54 ◇ q53))).trans (((cg (fun t => (q54 ◇ q53) ◇ t) (cg (fun t => (q54 ◇ q53) ◇ t) (apc31 q53))).trans (cg (fun t => (q54 ◇ q53) ◇ t) (apc33 q53 q54 ((q54 ◇ q53) ◇ (q53 ◇ q53)) ((q54 ◇ q53) ◇ (q53 ◇ q53))))).trans (apc13 q53 q54)))
  have apc44:=fun (q55 q56:G)=>by
    exact (((((cg (fun t => t ◇ ((q55 ◇ q56) ◇ (q56 ◇ q55))) (cg (fun t => (q56 ◇ q55) ◇ t) (apc35 ((q56 ◇ q55) ◇ (q56 ◇ q55)) ((q56 ◇ q55) ◇ (q56 ◇ q55)) ((q56 ◇ q55) ◇ (q56 ◇ q55)) q55 q56 ((q56 ◇ q55) ◇ (q56 ◇ q55))))).trans (apc15 q55 q56 (q56 ◇ q55))).trans (apc39 q55 q56)).symm).trans ((((cg (fun t => t ◇ ((q55 ◇ q56) ◇ (q56 ◇ q55))) (apc30 (q56 ◇ q55))).symm).trans (apc2 q55 q56 ((q56 ◇ q55) ◇ (q56 ◇ q55)))).trans (cg (fun t => (q56 ◇ q55) ◇ t) (apc35 ((q56 ◇ q55) ◇ (q56 ◇ q55)) ((q56 ◇ q55) ◇ (q56 ◇ q55)) ((q56 ◇ q55) ◇ (q56 ◇ q55)) q55 q56 ((q56 ◇ q55) ◇ (q56 ◇ q55)))))).symm
  have apc45:=fun (q57 q58:G)=>by
    exact (((cg (fun t => (q58 ◇ q58) ◇ t) (apc34 q57 q58)).symm).trans (apc38 (q57 ◇ q58) (q58 ◇ q58))).trans (apc33 q58 q58 ((q58 ◇ q58) ◇ (q58 ◇ q58)) ((q58 ◇ q58) ◇ (q58 ◇ q58)))
  have apc46:=fun (q59 q60:G)=>by
    exact ((cg (fun t => t ◇ ((q59 ◇ q60) ◇ (q60 ◇ q59))) (apc38 q59 q60)).symm).trans (apc2 q59 q60 q60)
  have apc47:=fun (q61 q62:G)=>by
    exact (((((((cg (fun t => ((q62 ◇ q62) ◇ (q62 ◇ q62)) ◇ t) (cg (fun t => t ◇ ((q62 ◇ q61) ◇ (q62 ◇ q62))) (apc33 q62 q61 ((q61 ◇ q62) ◇ (q62 ◇ q62)) ((q61 ◇ q62) ◇ (q62 ◇ q62))))).trans (cg (fun t => t ◇ ((q62 ◇ q61) ◇ ((q62 ◇ q61) ◇ (q62 ◇ q62)))) (apc33 q62 q62 ((q62 ◇ q62) ◇ (q62 ◇ q62)) ((q62 ◇ q62) ◇ (q62 ◇ q62))))).trans (cg (fun t => (q62 ◇ q62) ◇ t) (apc38 (q62 ◇ q62) (q62 ◇ q61)))).trans (cg (fun t => (q62 ◇ q62) ◇ t) (apc35 ((q62 ◇ q61) ◇ (q62 ◇ q61)) ((q62 ◇ q61) ◇ (q62 ◇ q61)) ((q62 ◇ q61) ◇ (q62 ◇ q61)) q61 q62 ((q62 ◇ q61) ◇ (q62 ◇ q61))))).trans (apc46 q61 q62)).symm).trans ((((cg (fun t => ((q62 ◇ q62) ◇ (q62 ◇ q62)) ◇ t) (cg (fun t => ((q61 ◇ q62) ◇ (q62 ◇ q62)) ◇ t) (apc34 q61 q62))).symm).trans (apc46 (q61 ◇ q62) (q62 ◇ q62))).trans ((cg (fun t => t ◇ (q62 ◇ q62)) (apc34 q61 q62)).trans (apc29 q62 (q62 ◇ q61))))).symm
  have apc48:=fun (q63 q64:G)=>by
    exact ((((cg (fun t => t ◇ ((q64 ◇ q63) ◇ (q64 ◇ q64))) (apc33 q64 q64 ((q64 ◇ q64) ◇ (q64 ◇ q64)) ((q64 ◇ q64) ◇ (q64 ◇ q64)))).trans (apc45 q63 q64)).symm).trans ((((cg (fun t => ((q64 ◇ q64) ◇ (q64 ◇ q64)) ◇ t) (apc34 q63 q64)).symm).trans (apc47 (q63 ◇ q64) (q64 ◇ q64))).trans (((cg (fun t => t ◇ (q64 ◇ q64)) (apc34 q63 q64)).trans (apc29 q64 (q64 ◇ q63))).trans (apc47 q63 q64)))).symm
  have apc49:=fun (q61 q62 q63 q64:G)=>by
    exact (apc47 q61 q62).trans (apc48 q61 q62)
  have apc51:=fun (q65 q66:G)=>by
    exact (((apc49 q65 q66 ((q66 ◇ q66) ◇ (q66 ◇ q65)) ((q66 ◇ q66) ◇ (q66 ◇ q65))).symm).trans ((((cg (fun t => t ◇ (q66 ◇ q65)) (apc48 q65 q66)).symm).trans (apc48 q66 (q66 ◇ q65))).trans (apc35 ((q66 ◇ q65) ◇ (q66 ◇ q65)) ((q66 ◇ q65) ◇ (q66 ◇ q65)) ((q66 ◇ q65) ◇ (q66 ◇ q65)) q65 q66 ((q66 ◇ q65) ◇ (q66 ◇ q65))))).symm
  have apc52:=fun (q21 q22 q65 q66:G)=>by
    exact (((apc51 q22 q21).symm).trans ((apc13 q21 q22).trans (apc51 q21 q22))).symm
  have apc53:=fun (q67 q68:G)=>by
    exact ((cg (fun t => q68 ◇ t) (apc52 q67 q68 q67 q67)).symm).trans (apc38 q68 q68)
  have apc55:=fun (q55 q56 q65 q66:G)=>by
    exact ((apc53 q56 (q56 ◇ q55)).symm).trans (((cg (fun t => (q56 ◇ q55) ◇ t) (apc51 q55 q56)).symm).trans ((apc44 q55 q56).trans (apc51 q55 q56)))
  have apc56:=fun (q69 q70:G)=>by
    exact ((apc33 q70 q69 ((q69 ◇ q70) ◇ (q70 ◇ q70)) ((q69 ◇ q70) ◇ (q70 ◇ q70))).symm).trans ((((cg (fun t => (q69 ◇ q70) ◇ t) (apc51 q69 q70)).symm).trans (apc38 (q70 ◇ q69) (q69 ◇ q70))).trans (apc55 q70 q69 ((q69 ◇ q70) ◇ (q69 ◇ q70)) ((q69 ◇ q70) ◇ (q69 ◇ q70))))
  have apc58:=fun (q71 q72 q73:G)=>by
    exact (((cg (fun t => t ◇ (q71 ◇ q71)) (apc56 q72 q73)).trans (apc56 (q71 ◇ q71) (q72 ◇ q72))).symm).trans (((cg (fun t => (q73 ◇ q72) ◇ t) (apc52 q71 q72 q71 q71)).symm).trans (apc33 q72 q73 q71 q71))
  exact ((apc58 ((x ◇ y) ◇ y) (x ◇ y) y).symm).trans (apc58 ((x ◇ y) ◇ y) z (x ◇ (w ◇ y)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47151_to_58633 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47151_to_58633
