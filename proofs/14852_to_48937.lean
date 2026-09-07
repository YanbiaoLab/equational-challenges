-- Equation14852 → Equation48937
-- Recorded verdict: true
-- Premise: x = y * (((z * x) * (x * y)) * y)
-- Conclusion: x * y = ((y * y) * x) * (x * y)
-- Original submission SHA-256: 7f77a9570e95a5748c93a075e57c4ac9d312758f2d97c55b3ee14d4977482046
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (((z ◇ x) ◇ (x ◇ y)) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = ((y ◇ y) ◇ x) ◇ (x ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc2 : forall (q0 q1 q2 q3:G), (q2 ◇ ((q0 ◇ ((((q1 ◇ q0) ◇ (q0 ◇ q3)) ◇ q3) ◇ q2)) ◇ q2)) = (((q1 ◇ q0) ◇ (q0 ◇ q3)) ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ ((((q1 ◇ q0) ◇ (q0 ◇ q3)) ◇ q3) ◇ q2)) ((h q0 q3 q1).symm)))).symm).trans ((h (((q1 ◇ q0) ◇ (q0 ◇ q3)) ◇ q3) q2 q3).symm)
  have apc3 : forall (q0 q1 q4 q3:G), ((((q1 ◇ q0) ◇ (q0 ◇ q4)) ◇ q4) ◇ (((q3 ◇ q4) ◇ q0) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q4)) ◇ q4))) = q4:=by
    intro q0 q1 q4 q3
    exact ((cg (fun t => (((q1 ◇ q0) ◇ (q0 ◇ q4)) ◇ q4) ◇ t) (cg (fun t => t ◇ (((q1 ◇ q0) ◇ (q0 ◇ q4)) ◇ q4)) (cg (fun t => (q3 ◇ q4) ◇ t) ((h q0 q4 q1).symm)))).symm).trans ((h q4 (((q1 ◇ q0) ◇ (q0 ◇ q4)) ◇ q4) q3).symm)
  have apc7 : forall (q5 q6 q7 q8 q9:G), (q8 ◇ (((((q6 ◇ q5) ◇ (q5 ◇ q7)) ◇ q7) ◇ (((q5 ◇ ((((q6 ◇ q5) ◇ (q5 ◇ q7)) ◇ q7) ◇ q9)) ◇ q9) ◇ q8)) ◇ q8)) = ((q5 ◇ ((((q6 ◇ q5) ◇ (q5 ◇ q7)) ◇ q7) ◇ q9)) ◇ q9):=by
    intro q5 q6 q7 q8 q9
    exact ((cg (fun t => q8 ◇ t) (cg (fun t => t ◇ q8) (cg (fun t => t ◇ (((q5 ◇ ((((q6 ◇ q5) ◇ (q5 ◇ q7)) ◇ q7) ◇ q9)) ◇ q9) ◇ q8)) (apc2 q5 q6 q9 q7)))).symm).trans ((h ((q5 ◇ ((((q6 ◇ q5) ◇ (q5 ◇ q7)) ◇ q7) ◇ q9)) ◇ q9) q8 q9).symm)
  have apc16 : forall (q10 q11 q12 q13 q14 q15:G), (q15 ◇ ((q13 ◇ ((((q14 ◇ q13) ◇ (((q11 ◇ q10) ◇ (q10 ◇ q12)) ◇ q12)) ◇ ((q10 ◇ ((((q11 ◇ q10) ◇ (q10 ◇ q12)) ◇ q12) ◇ q13)) ◇ q13)) ◇ q15)) ◇ q15)) = (((q14 ◇ q13) ◇ (((q11 ◇ q10) ◇ (q10 ◇ q12)) ◇ q12)) ◇ ((q10 ◇ ((((q11 ◇ q10) ◇ (q10 ◇ q12)) ◇ q12) ◇ q13)) ◇ q13)):=by
    intro q10 q11 q12 q13 q14 q15
    exact (((cg (fun t => q15 ◇ t) (cg (fun t => t ◇ q15) (cg (fun t => q13 ◇ t) (cg (fun t => t ◇ q15) (cg (fun t => t ◇ ((q10 ◇ ((((q11 ◇ q10) ◇ (q10 ◇ q12)) ◇ q12) ◇ q13)) ◇ q13)) (cg (fun t => (q14 ◇ q13) ◇ t) (apc2 q10 q11 q13 q12))))))).symm).trans (apc2 q13 q14 q15 ((q10 ◇ ((((q11 ◇ q10) ◇ (q10 ◇ q12)) ◇ q12) ◇ q13)) ◇ q13))).trans (cg (fun t => t ◇ ((q10 ◇ ((((q11 ◇ q10) ◇ (q10 ◇ q12)) ◇ q12) ◇ q13)) ◇ q13)) (cg (fun t => (q14 ◇ q13) ◇ t) (apc2 q10 q11 q13 q12)))
  have apc19 : forall (q16 q17 q18 q19 q20:G), (q20 ◇ ((q18 ◇ ((q16 ◇ ((q16 ◇ ((((q17 ◇ q16) ◇ (q16 ◇ (q19 ◇ q18))) ◇ (q19 ◇ q18)) ◇ q18)) ◇ q18)) ◇ q20)) ◇ q20)) = (((q19 ◇ q18) ◇ (((q17 ◇ q16) ◇ (q16 ◇ (q19 ◇ q18))) ◇ (q19 ◇ q18))) ◇ ((q16 ◇ ((((q17 ◇ q16) ◇ (q16 ◇ (q19 ◇ q18))) ◇ (q19 ◇ q18)) ◇ q18)) ◇ q18)):=by
    intro q16 q17 q18 q19 q20
    exact ((cg (fun t => q20 ◇ t) (cg (fun t => t ◇ q20) (cg (fun t => q18 ◇ t) (cg (fun t => t ◇ q20) (cg (fun t => t ◇ ((q16 ◇ ((((q17 ◇ q16) ◇ (q16 ◇ (q19 ◇ q18))) ◇ (q19 ◇ q18)) ◇ q18)) ◇ q18)) ((h q16 (q19 ◇ q18) q17).symm)))))).symm).trans (apc16 q16 q17 (q19 ◇ q18) q18 q19 q20)
  have apc21 : forall (q21 q22 q23:G), (((q23 ◇ q22) ◇ (((q21 ◇ q22) ◇ (q22 ◇ (q23 ◇ q22))) ◇ (q23 ◇ q22))) ◇ ((q22 ◇ ((((q21 ◇ q22) ◇ (q22 ◇ (q23 ◇ q22))) ◇ (q23 ◇ q22)) ◇ q22)) ◇ q22)) = (((q21 ◇ q22) ◇ (q22 ◇ (q23 ◇ q22))) ◇ (q23 ◇ q22)):=by
    intro q21 q22 q23
    exact (((apc2 q22 q21 q21 (q23 ◇ q22)).symm).trans (((cg (fun t => q21 ◇ t) (cg (fun t => t ◇ q21) (cg (fun t => q22 ◇ t) (cg (fun t => t ◇ q21) (apc2 q22 q21 q22 (q23 ◇ q22)))))).symm).trans (apc19 q22 q21 q22 q23 q21))).symm
  have apc22 : forall (q5 q6 q7 q24 q9:G), (((q5 ◇ ((((q6 ◇ q5) ◇ (q5 ◇ q7)) ◇ q7) ◇ q24)) ◇ q24) ◇ (((q9 ◇ q24) ◇ (((q6 ◇ q5) ◇ (q5 ◇ q7)) ◇ q7)) ◇ ((q5 ◇ ((((q6 ◇ q5) ◇ (q5 ◇ q7)) ◇ q7) ◇ q24)) ◇ q24))) = q24:=by
    intro q5 q6 q7 q24 q9
    exact ((cg (fun t => ((q5 ◇ ((((q6 ◇ q5) ◇ (q5 ◇ q7)) ◇ q7) ◇ q24)) ◇ q24) ◇ t) (cg (fun t => t ◇ ((q5 ◇ ((((q6 ◇ q5) ◇ (q5 ◇ q7)) ◇ q7) ◇ q24)) ◇ q24)) (cg (fun t => (q9 ◇ q24) ◇ t) (apc2 q5 q6 q24 q7)))).symm).trans ((h q24 ((q5 ◇ ((((q6 ◇ q5) ◇ (q5 ◇ q7)) ◇ q7) ◇ q24)) ◇ q24) q9).symm)
  have apc23 : forall (q25 q26 q27:G), (((q25 ◇ ((((q26 ◇ q25) ◇ (q25 ◇ (q27 ◇ q25))) ◇ (q27 ◇ q25)) ◇ q25)) ◇ q25) ◇ (((q26 ◇ q25) ◇ (q25 ◇ (q27 ◇ q25))) ◇ (q27 ◇ q25))) = q25:=by
    intro q25 q26 q27
    exact ((cg (fun t => ((q25 ◇ ((((q26 ◇ q25) ◇ (q25 ◇ (q27 ◇ q25))) ◇ (q27 ◇ q25)) ◇ q25)) ◇ q25) ◇ t) (apc21 q26 q25 q27)).symm).trans (apc22 q25 q26 (q27 ◇ q25) q25 q27)
  have apc24 : forall (q28 q29 q30:G), ((q30 ◇ ((((q29 ◇ q30) ◇ (q30 ◇ (q28 ◇ q30))) ◇ (q28 ◇ q30)) ◇ q30)) ◇ q30) = (q28 ◇ q30):=by
    intro q28 q29 q30
    exact (((apc3 q30 q29 (q28 ◇ q30) ((q29 ◇ q30) ◇ (q30 ◇ (q28 ◇ q30)))).symm).trans (((cg (fun t => (((q29 ◇ q30) ◇ (q30 ◇ (q28 ◇ q30))) ◇ (q28 ◇ q30)) ◇ t) (cg (fun t => t ◇ (((q29 ◇ q30) ◇ (q30 ◇ (q28 ◇ q30))) ◇ (q28 ◇ q30))) (cg (fun t => (((q29 ◇ q30) ◇ (q30 ◇ (q28 ◇ q30))) ◇ (q28 ◇ q30)) ◇ t) (apc23 q30 q29 q28)))).symm).trans (apc7 q30 q29 (q28 ◇ q30) (((q29 ◇ q30) ◇ (q30 ◇ (q28 ◇ q30))) ◇ (q28 ◇ q30)) q30))).symm
  have apc25 : forall (q31 q32 q33:G), (((q32 ◇ q33) ◇ (q33 ◇ (q31 ◇ q33))) ◇ (q31 ◇ q33)) = (q33 ◇ (q31 ◇ q33)):=by
    intro q31 q32 q33
    exact (((cg (fun t => q33 ◇ t) (apc24 q31 q32 q33)).symm).trans (apc2 q33 q32 q33 (q31 ◇ q33))).symm
  have apc26 : forall (q34 q35:G), ((q34 ◇ q35) ◇ (q35 ◇ (q34 ◇ q35))) = q35:=by
    intro q34 q35
    exact ((cg (fun t => (q34 ◇ q35) ◇ t) (apc25 q34 q34 q35)).symm).trans ((h q35 (q34 ◇ q35) q34).symm)
  have apc28 : forall (q36 q37 q38:G), (((q37 ◇ q36) ◇ (q36 ◇ q38)) ◇ q38) = (q36 ◇ q38):=by
    intro q36 q37 q38
    exact (((cg (fun t => q36 ◇ t) (apc26 ((q37 ◇ q36) ◇ (q36 ◇ q38)) q38)).symm).trans (((cg (fun t => t ◇ ((((q37 ◇ q36) ◇ (q36 ◇ q38)) ◇ q38) ◇ (q38 ◇ (((q37 ◇ q36) ◇ (q36 ◇ q38)) ◇ q38)))) ((h q36 q38 q37).symm)).symm).trans (apc26 q38 (((q37 ◇ q36) ◇ (q36 ◇ q38)) ◇ q38)))).symm
  have apc29 : forall (x y z q36 q37 q38:G), (y ◇ (x ◇ y)) = x:=by
    intro x y z q36 q37 q38
    exact ((h x y x).trans (cg (fun t => y ◇ t) (apc28 x x y))).symm
  have apc30 : forall (x y z q36 q37 q38 q34 q35:G), ((q34 ◇ q35) ◇ q34) = q35:=by
    intro x y z q36 q37 q38 q34 q35
    exact ((cg (fun t => (q34 ◇ q35) ◇ t) (apc29 q34 q35 (q35 ◇ (q34 ◇ q35)) (q35 ◇ (q34 ◇ q35)) (q35 ◇ (q34 ◇ q35)) (q35 ◇ (q34 ◇ q35)))).symm).trans (apc26 q34 q35)
  have apc31 : forall (q39 q40 q41:G), (q40 ◇ q39) = q41:=by
    intro q39 q40 q41
    exact ((apc29 (q40 ◇ q39) (q39 ◇ q41) ((q39 ◇ q41) ◇ ((q40 ◇ q39) ◇ (q39 ◇ q41))) ((q39 ◇ q41) ◇ ((q40 ◇ q39) ◇ (q39 ◇ q41))) ((q39 ◇ q41) ◇ ((q40 ◇ q39) ◇ (q39 ◇ q41))) ((q39 ◇ q41) ◇ ((q40 ◇ q39) ◇ (q39 ◇ q41)))).symm).trans (((cg (fun t => t ◇ ((q40 ◇ q39) ◇ (q39 ◇ q41))) (apc28 q39 q40 q41)).symm).trans (apc30 q39 q39 q39 q39 q39 q39 ((q40 ◇ q39) ◇ (q39 ◇ q41)) q41))
  exact (apc31 y x (x ◇ y)).trans ((apc31 (x ◇ y) ((y ◇ y) ◇ x) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_14852_to_48937 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_14852_to_48937
