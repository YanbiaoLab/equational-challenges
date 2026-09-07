-- Equation54055 → Equation54703
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ x) = y ◇ (x ◇ (z ◇ z))
-- Conclusion: x ◇ (x ◇ x) = y ◇ ((x ◇ y) ◇ y)
-- Original submission SHA-256: 1bd69484a23d7529bb6bec30e7385d2dc4439f0a752289a9feff2c8d07d8fb68
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ x) = y ◇ (x ◇ (z ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ x) = y ◇ ((x ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ ((q0 ◇ q0) ◇ (q1 ◇ (q0 ◇ q0)))) = (q1 ◇ (q2 ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) ((h (q0 ◇ q0) q1 q0).symm)).symm).trans ((h q1 q2 (q0 ◇ q0)).symm)
  have apc1 : forall (x y z:G), (y ◇ (x ◇ (z ◇ z))) = (y ◇ (x ◇ (x ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc2 : forall (q3 q4 q5:G), (q5 ◇ ((q3 ◇ q3) ◇ (q4 ◇ (q4 ◇ q4)))) = (q4 ◇ (q5 ◇ q4)):=by
    intro q3 q4 q5
    exact ((cg (fun t => q5 ◇ t) (apc1 q4 (q3 ◇ q3) q3)).symm).trans (apc0 q3 q4 q5)
  have apc3 : forall (q6 q7:G), (q7 ◇ (q6 ◇ (q6 ◇ q6))) = (q6 ◇ (q7 ◇ q6)):=by
    intro q6 q7
    exact ((apc1 q6 q7 q6).symm).trans ((h q6 q7 q6).symm)
  have apc4 : forall (q8 q9 q10:G), (q10 ◇ (q9 ◇ ((q8 ◇ q8) ◇ q9))) = (q9 ◇ (q10 ◇ q9)):=by
    intro q8 q9 q10
    exact ((cg (fun t => q10 ◇ t) ((h q9 (q8 ◇ q8) q8).symm)).symm).trans (apc0 q8 q9 q10)
  have apc5 : forall (q11 q0 q1 q2:G), (q2 ◇ (q1 ◇ (q11 ◇ ((q11 ◇ (q0 ◇ q0)) ◇ q11)))) = (q1 ◇ (q2 ◇ q1)):=by
    intro q11 q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) ((h q11 (q11 ◇ (q0 ◇ q0)) q0).symm))).symm).trans ((h q1 q2 (q11 ◇ (q0 ◇ q0))).symm)
  have apc6 : forall (q12 q13 q14 q15:G), (q15 ◇ (q14 ◇ ((q12 ◇ ((q12 ◇ (q13 ◇ q13)) ◇ q12)) ◇ q14))) = (q14 ◇ (q15 ◇ q14)):=by
    intro q12 q13 q14 q15
    exact ((cg (fun t => q15 ◇ t) (apc3 q14 (q12 ◇ ((q12 ◇ (q13 ◇ q13)) ◇ q12)))).symm).trans (((cg (fun t => q15 ◇ t) (cg (fun t => t ◇ (q14 ◇ (q14 ◇ q14))) ((h q12 (q12 ◇ (q13 ◇ q13)) q13).symm))).symm).trans (apc2 (q12 ◇ (q13 ◇ q13)) q14 q15))
  have apc7 : forall (q16 q17 q18 q19:G), (q19 ◇ (q18 ◇ (q17 ◇ ((q17 ◇ ((q16 ◇ q16) ◇ q17)) ◇ q17)))) = (q18 ◇ (q19 ◇ q18)):=by
    intro q16 q17 q18 q19
    exact ((cg (fun t => q19 ◇ t) (cg (fun t => q18 ◇ t) (apc4 q16 q17 (q17 ◇ ((q16 ◇ q16) ◇ q17))))).symm).trans ((h q18 q19 (q17 ◇ ((q16 ◇ q16) ◇ q17))).symm)
  have apc8 : forall (q20 q21 q22 q23 q24:G), (q23 ◇ ((q20 ◇ (q21 ◇ q21)) ◇ (q22 ◇ (q20 ◇ (q21 ◇ q21))))) = (q22 ◇ (q23 ◇ q22)):=by
    intro q20 q21 q22 q23 q24
    exact (((cg (fun t => q23 ◇ t) (cg (fun t => q22 ◇ t) (cg (fun t => (q20 ◇ (q21 ◇ q21)) ◇ t) (cg (fun t => t ◇ (q20 ◇ (q21 ◇ q21))) (apc4 q24 q20 (q20 ◇ (q21 ◇ q21))))))).trans (cg (fun t => q23 ◇ t) (apc6 q20 q21 (q20 ◇ (q21 ◇ q21)) q22))).symm).trans (((cg (fun t => q23 ◇ t) (cg (fun t => q22 ◇ t) (cg (fun t => (q20 ◇ (q21 ◇ q21)) ◇ t) (cg (fun t => t ◇ (q20 ◇ (q21 ◇ q21))) (cg (fun t => (q20 ◇ (q21 ◇ q21)) ◇ t) ((h q20 (q24 ◇ q24) q21).symm)))))).symm).trans (apc7 q24 (q20 ◇ (q21 ◇ q21)) q22 q23))
  have apc9 : forall (q25 q26 q27 q28:G), (q28 ◇ ((q25 ◇ (q26 ◇ q26)) ◇ (q25 ◇ (q27 ◇ q25)))) = (q27 ◇ (q28 ◇ q27)):=by
    intro q25 q26 q27 q28
    exact ((cg (fun t => q28 ◇ t) (cg (fun t => (q25 ◇ (q26 ◇ q26)) ◇ t) ((h q25 q27 q26).symm))).symm).trans (apc8 q25 q26 q27 q28 q25)
  have apc10 : forall (q29 q30 q31:G), (q31 ◇ (q29 ◇ (q30 ◇ q29))) = (q30 ◇ (q31 ◇ q30)):=by
    intro q29 q30 q31
    exact ((cg (fun t => q31 ◇ t) (apc9 q29 q29 q29 q30)).symm).trans ((h q30 q31 (q29 ◇ (q29 ◇ q29))).symm)
  have apc12 : forall (q32 q33 q34 q35:G), (q35 ◇ ((q32 ◇ ((q32 ◇ (q33 ◇ q33)) ◇ q32)) ◇ q35)) = (q34 ◇ (q35 ◇ q34)):=by
    intro q32 q33 q34 q35
    exact ((apc5 q32 q33 q35 (q32 ◇ ((q32 ◇ (q33 ◇ q33)) ◇ q32))).symm).trans (((apc10 q34 (q32 ◇ ((q32 ◇ (q33 ◇ q33)) ◇ q32)) q35).symm).trans (apc6 q32 q33 q34 q35))
  have apc13 : forall (q32 q33 q34 q35:G), (q34 ◇ (q35 ◇ q34)) = (q32 ◇ (q35 ◇ q32)):=by
    intro q32 q33 q34 q35
    exact ((apc12 q32 q33 q34 q35).symm).trans (apc12 q32 q33 q32 q35)
  have apc14 : forall (q36 q37 q38:G), (q37 ◇ ((q38 ◇ q38) ◇ q37)) = (q36 ◇ (q37 ◇ q36)):=by
    intro q36 q37 q38
    exact (((apc13 q36 q36 (q38 ◇ q38) q37).symm).trans ((h q37 (q38 ◇ q38) q38).symm)).symm
  have apc15 : forall (q39 q40 q41 q42:G), (q41 ◇ ((q40 ◇ q40) ◇ q41)) = (q39 ◇ (q42 ◇ q39)):=by
    intro q39 q40 q41 q42
    exact (((apc14 q39 q42 q40).symm).trans (apc13 q41 q39 q42 (q40 ◇ q40))).symm
  exact ((apc15 x (x ◇ (x ◇ x)) (y ◇ ((x ◇ y) ◇ y)) x).symm).trans (apc15 y (x ◇ (x ◇ x)) (y ◇ ((x ◇ y) ◇ y)) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_54055_to_54703 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_54055_to_54703
