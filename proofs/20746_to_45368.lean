-- Equation20746 → Equation45368
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ (((y ◇ z) ◇ y) ◇ y)
-- Conclusion: x ◇ y = x ◇ (((z ◇ w) ◇ x) ◇ w)
-- Original submission SHA-256: 7ad142f4dfc4ab3e6f6bb3bb210f9085f10ae30d7fe5d98496df210e1ed8b72b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ (((y ◇ z) ◇ y) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = x ◇ (((z ◇ w) ◇ x) ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc2 : forall (q0 q1 q2 q3:G), (q0 ◇ ((((q1 ◇ q0) ◇ q3) ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0))) = (((q1 ◇ q2) ◇ q1) ◇ q1):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ ((((q1 ◇ q0) ◇ q3) ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0))) ((h q0 q1 q2).symm)).symm).trans ((h (((q1 ◇ q2) ◇ q1) ◇ q1) (q1 ◇ q0) q3).symm)
  have apc3 : forall (q4 q5 q6 q7:G), ((q7 ◇ q6) ◇ (((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q7) ◇ q7)) = q6:=by
    intro q4 q5 q6 q7
    exact ((cg (fun t => (q7 ◇ q6) ◇ t) (cg (fun t => t ◇ q7) (cg (fun t => t ◇ q7) (apc2 q7 q4 q5 q4)))).symm).trans ((h q6 q7 ((((q4 ◇ q7) ◇ q4) ◇ (q4 ◇ q7)) ◇ (q4 ◇ q7))).symm)
  have apc4 : forall (q8 q9 q10:G), (q8 ◇ ((q8 ◇ (q9 ◇ q8)) ◇ (q9 ◇ q8))) = (((q9 ◇ q10) ◇ q9) ◇ q9):=by
    intro q8 q9 q10
    exact ((cg (fun t => q8 ◇ t) (cg (fun t => t ◇ (q9 ◇ q8)) (cg (fun t => t ◇ (q9 ◇ q8)) ((h q8 q9 q8).symm)))).symm).trans (apc2 q8 q9 q10 (((q9 ◇ q8) ◇ q9) ◇ q9))
  have apc5 : forall (q0 q1 q11:G), (((q1 ◇ q0) ◇ q11) ◇ ((q0 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0))) = q11:=by
    intro q0 q1 q11
    exact ((cg (fun t => ((q1 ◇ q0) ◇ q11) ◇ t) (cg (fun t => t ◇ (q1 ◇ q0)) (cg (fun t => t ◇ (q1 ◇ q0)) ((h q0 q1 q0).symm)))).symm).trans ((h q11 (q1 ◇ q0) (((q1 ◇ q0) ◇ q1) ◇ q1)).symm)
  have apc6 : forall (q12 q13 q14:G), (((((q13 ◇ q12) ◇ q13) ◇ q13) ◇ q14) ◇ (((q13 ◇ q12) ◇ q13) ◇ q13)) = q14:=by
    intro q12 q13 q14
    exact ((cg (fun t => ((((q13 ◇ q12) ◇ q13) ◇ q13) ◇ q14) ◇ t) ((h (((q13 ◇ q12) ◇ q13) ◇ q13) q13 q12).symm)).symm).trans (apc5 q13 ((q13 ◇ q12) ◇ q13) q14)
  have apc7 : forall (q15 q16:G), ((q16 ◇ ((q16 ◇ q15) ◇ q16)) ◇ ((q16 ◇ q15) ◇ q16)) = (q16 ◇ (((q16 ◇ q15) ◇ q16) ◇ q16)):=by
    intro q15 q16
    exact (((cg (fun t => t ◇ (((q16 ◇ q15) ◇ q16) ◇ q16)) (apc5 q16 (q16 ◇ q15) q16)).symm).trans (apc6 q15 q16 ((q16 ◇ ((q16 ◇ q15) ◇ q16)) ◇ ((q16 ◇ q15) ◇ q16)))).symm
  have apc8 : forall (q17 q18 q19 q20 q21:G), ((q21 ◇ q20) ◇ (((q19 ◇ (((q18 ◇ q17) ◇ q18) ◇ q18)) ◇ q21) ◇ q21)) = q20:=by
    intro q17 q18 q19 q20 q21
    exact ((cg (fun t => (q21 ◇ q20) ◇ t) (cg (fun t => t ◇ q21) (cg (fun t => t ◇ q21) (cg (fun t => t ◇ (((q18 ◇ q17) ◇ q18) ◇ q18)) (apc6 q17 q18 q19))))).symm).trans (apc3 (((q18 ◇ q17) ◇ q18) ◇ q18) q19 q20 q21)
  have apc9 : forall (q22 q23 q24:G), ((q24 ◇ q23) ◇ ((q22 ◇ q24) ◇ q24)) = q23:=by
    intro q22 q23 q24
    exact ((cg (fun t => (q24 ◇ q23) ◇ t) (cg (fun t => t ◇ q24) (cg (fun t => t ◇ q24) ((h q22 q22 q22).symm)))).symm).trans (apc8 q22 q22 (q22 ◇ q22) q23 q24)
  have apc10 : forall (q25:G), (q25 ◇ (((q25 ◇ q25) ◇ q25) ◇ q25)) = ((q25 ◇ q25) ◇ q25):=by
    intro q25
    exact (((apc9 q25 ((q25 ◇ q25) ◇ q25) q25).symm).trans (apc7 q25 q25)).symm
  have apc11 : forall (q26 q27:G), (((q26 ◇ q27) ◇ q26) ◇ q26) = q26:=by
    intro q26 q27
    exact ((((cg (fun t => (((q26 ◇ q26) ◇ q26) ◇ q26) ◇ t) (cg (fun t => ((((q26 ◇ q26) ◇ q26) ◇ q26) ◇ ((q26 ◇ q26) ◇ q26)) ◇ t) (apc10 q26))).trans (apc9 (((q26 ◇ q26) ◇ q26) ◇ q26) q26 ((q26 ◇ q26) ◇ q26))).symm).trans (((cg (fun t => (((q26 ◇ q26) ◇ q26) ◇ q26) ◇ t) (cg (fun t => t ◇ (q26 ◇ (((q26 ◇ q26) ◇ q26) ◇ q26))) (cg (fun t => (((q26 ◇ q26) ◇ q26) ◇ q26) ◇ t) (apc10 q26)))).symm).trans (apc4 (((q26 ◇ q26) ◇ q26) ◇ q26) q26 q27))).symm
  have apc13 : forall (q0 q1 q2 q3 q26 q27:G), (q0 ◇ (q1 ◇ q0)) = q1:=by
    intro q0 q1 q2 q3 q26 q27
    exact ((cg (fun t => q0 ◇ t) (apc11 (q1 ◇ q0) q3)).symm).trans ((apc2 q0 q1 q2 q3).trans (apc11 q1 q2))
  have apc14 : forall (q28 q29 q30:G), (q28 ◇ ((q29 ◇ q30) ◇ q30)) = (q28 ◇ q30):=by
    intro q28 q29 q30
    exact ((cg (fun t => t ◇ ((q29 ◇ q30) ◇ q30)) (apc13 q30 q28 q28 q28 q28 q28)).symm).trans (apc9 q29 (q28 ◇ q30) q30)
  have apc15 : forall (q31 q32 q33 q34:G), (q33 ◇ (q31 ◇ q32)) = (q33 ◇ q32):=by
    intro q31 q32 q33 q34
    exact ((cg (fun t => q33 ◇ t) (cg (fun t => q31 ◇ t) (apc11 q32 q34))).symm).trans ((((cg (fun t => q33 ◇ t) (cg (fun t => t ◇ (((q32 ◇ q34) ◇ q32) ◇ q32)) ((h q31 q32 q34).symm))).symm).trans (apc14 q33 (q32 ◇ q31) (((q32 ◇ q34) ◇ q32) ◇ q32))).trans (cg (fun t => q33 ◇ t) (apc11 q32 q34)))
  have apc18 : forall (q35 q36 q37 q38:G), (q37 ◇ q36) = (q37 ◇ q35):=by
    intro q35 q36 q37 q38
    exact ((((cg (fun t => q37 ◇ t) ((h q35 q36 q38).symm)).symm).trans (apc15 (q36 ◇ q35) (((q36 ◇ q38) ◇ q36) ◇ q36) q37 q35)).trans (cg (fun t => q37 ◇ t) (apc11 q36 q38))).symm
  exact (apc18 (x ◇ y) y x (x ◇ y)).trans ((apc18 (x ◇ y) (((z ◇ w) ◇ x) ◇ w) x (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_20746_to_45368 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_20746_to_45368
