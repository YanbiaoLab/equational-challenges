-- Equation17501 → Equation29027
-- Recorded verdict: true
-- Premise: x = (y * z) * (x * (y * (y * z)))
-- Conclusion: x = (((y * z) * y) * w) * (u * x)
-- Original submission SHA-256: f1c743beee900c9b6aff281e43c9b78a03f32ce947e38de3dbaad2aba7840779
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ (x ◇ (y ◇ (y ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (((y ◇ z) ◇ y) ◇ w) ◇ (u ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (((q0 ◇ q1) ◇ (q0 ◇ (q0 ◇ q1))) ◇ (q2 ◇ (q0 ◇ q1))) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q0 ◇ q1) ◇ (q0 ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => q2 ◇ t) ((h (q0 ◇ q1) q0 q1).symm))).symm).trans ((h q2 (q0 ◇ q1) (q0 ◇ (q0 ◇ q1))).symm)
  have apc1 : forall (q1 q3:G), ((q3 ◇ (q3 ◇ q1)) ◇ q3) = (q3 ◇ q1):=by
    intro q1 q3
    exact ((cg (fun t => (q3 ◇ (q3 ◇ q1)) ◇ t) ((h q3 q3 q1).symm)).symm).trans ((h (q3 ◇ q1) q3 (q3 ◇ q1)).symm)
  have apc2 : forall (q4 q5:G), ((q4 ◇ q5) ◇ (q4 ◇ (q4 ◇ q5))) = ((q4 ◇ q5) ◇ q4):=by
    intro q4 q5
    exact (((cg (fun t => (q4 ◇ q5) ◇ t) (apc0 q4 q5 q4)).symm).trans ((h ((q4 ◇ q5) ◇ (q4 ◇ (q4 ◇ q5))) q4 q5).symm)).symm
  have apc3 : forall (q0 q1 q2 q4 q5:G), (((q0 ◇ q1) ◇ q0) ◇ (q2 ◇ (q0 ◇ q1))) = q2:=by
    intro q0 q1 q2 q4 q5
    exact ((cg (fun t => t ◇ (q2 ◇ (q0 ◇ q1))) (apc2 q0 q1)).symm).trans (apc0 q0 q1 q2)
  have apc4 : forall (q6 q7 q8:G), ((((q6 ◇ q7) ◇ q6) ◇ q8) ◇ ((q6 ◇ q7) ◇ q6)) = q8:=by
    intro q6 q7 q8
    exact (((cg (fun t => t ◇ ((q6 ◇ q7) ◇ q6)) (cg (fun t => ((q6 ◇ q7) ◇ q6) ◇ t) (apc3 q6 q7 q8 q6 q6))).symm).trans (apc1 (q8 ◇ (q6 ◇ q7)) ((q6 ◇ q7) ◇ q6))).trans (apc3 q6 q7 q8 (((q6 ◇ q7) ◇ q6) ◇ (q8 ◇ (q6 ◇ q7))) (((q6 ◇ q7) ◇ q6) ◇ (q8 ◇ (q6 ◇ q7))))
  have apc6 : forall (q9 q10 q11:G), (((q10 ◇ q9) ◇ q11) ◇ (q10 ◇ q9)) = q11:=by
    intro q9 q10 q11
    exact ((cg (fun t => ((q10 ◇ q9) ◇ q11) ◇ t) (apc1 q9 q10)).symm).trans (((cg (fun t => t ◇ ((q10 ◇ (q10 ◇ q9)) ◇ q10)) (cg (fun t => t ◇ q11) (apc1 q9 q10))).symm).trans (apc4 q10 (q10 ◇ q9) q11))
  have apc7 : forall (q12 q13:G), (q13 ◇ (q13 ◇ q12)) = q13:=by
    intro q12 q13
    exact (((apc6 q12 q13 q13).symm).trans (((cg (fun t => t ◇ (q13 ◇ q12)) (apc2 q13 q12)).symm).trans (apc6 q12 q13 (q13 ◇ (q13 ◇ q12))))).symm
  have apc9 : forall (q14 q15 q16:G), ((q15 ◇ q16) ◇ (q14 ◇ q15)) = q14:=by
    intro q14 q15 q16
    exact ((cg (fun t => (q15 ◇ q16) ◇ t) (cg (fun t => q14 ◇ t) (apc7 q16 q15))).symm).trans ((h q14 q15 q16).symm)
  have apc11 : forall (q17 q0 q1 q2:G), (q17 ◇ (q2 ◇ ((q0 ◇ q1) ◇ q17))) = q2:=by
    intro q17 q0 q1 q2
    exact (((cg (fun t => q17 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => q17 ◇ t) (apc7 q1 q0)))))).trans (cg (fun t => q17 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (apc9 q17 q0 q1))))).symm).trans (((cg (fun t => t ◇ (q2 ◇ ((q0 ◇ q1) ◇ ((q0 ◇ q1) ◇ (q17 ◇ (q0 ◇ (q0 ◇ q1))))))) ((h q17 q0 q1).symm)).symm).trans ((h q2 (q0 ◇ q1) (q17 ◇ (q0 ◇ (q0 ◇ q1)))).symm))
  have apc12 : forall (q18 q19 q20 q21 q22:G), (((q18 ◇ q19) ◇ q22) ◇ (q20 ◇ q21)) = q22:=by
    intro q18 q19 q20 q21 q22
    exact ((cg (fun t => ((q18 ◇ q19) ◇ q22) ◇ t) (apc11 q22 q18 q19 (q20 ◇ q21))).symm).trans (apc11 ((q18 ◇ q19) ◇ q22) q20 q21 q22)
  have apc13 : forall (q23 q24 q25 q26:G), ((q23 ◇ q26) ◇ (q24 ◇ q25)) = q26:=by
    intro q23 q24 q25 q26
    exact ((cg (fun t => t ◇ (q24 ◇ q25)) (cg (fun t => t ◇ q26) (apc12 q23 q23 q23 q23 q23))).symm).trans (apc12 ((q23 ◇ q23) ◇ q23) (q23 ◇ q23) q24 q25 q26)
  have apc14 : forall (q23 q27 q28 q26:G), (((q27 ◇ q28) ◇ q26) ◇ q23) = q26:=by
    intro q23 q27 q28 q26
    exact ((cg (fun t => ((q27 ◇ q28) ◇ q26) ◇ t) (apc12 q23 q23 q23 q23 q23)).symm).trans (apc12 q27 q28 ((q23 ◇ q23) ◇ q23) (q23 ◇ q23) q26)
  have apc15 : forall (q29 q30 q31 q32:G), (q29 ◇ (q30 ◇ q31)) = q32:=by
    intro q29 q30 q31 q32
    exact ((cg (fun t => t ◇ (q30 ◇ q31)) (apc14 q32 q29 q29 q29)).symm).trans (apc13 ((q29 ◇ q29) ◇ q29) q30 q31 q32)
  have apc19 : forall (q33 q34 q35:G), ((q34 ◇ q35) ◇ q33) = q35:=by
    intro q33 q34 q35
    exact ((cg (fun t => (q34 ◇ q35) ◇ t) (apc13 q33 q33 q33 q33)).symm).trans (apc13 q34 (q33 ◇ q33) (q33 ◇ q33) q35)
  have apc20 : forall (q36 q37 q38 q39:G), q37 = q36:=by
    intro q36 q37 q38 q39
    exact ((apc19 q38 q39 q37).symm).trans (((cg (fun t => (q39 ◇ q37) ◇ t) (apc15 q36 q39 (q39 ◇ q37) q38)).symm).trans ((h q36 q39 q37).symm))
  exact (apc20 x x x x).trans ((apc20 x ((((y ◇ z) ◇ y) ◇ w) ◇ (u ◇ x)) x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_17501_to_29027 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_17501_to_29027
