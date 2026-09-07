-- Equation24451 → Equation28091
-- Recorded verdict: true
-- Premise: x = ((y * y) * z) * ((z * x) * x)
-- Conclusion: x = ((y * (z * y)) * x) * (w * x)
-- Original submission SHA-256: 266424908b0a28c89e50a4f51e18cdf4390f38f596505d15f371707c313697bd
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ z) ◇ ((z ◇ x) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ y)) ◇ x) ◇ (w ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), ((q0 ◇ q2) ◇ ((q2 ◇ q1) ◇ q1)) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ ((q2 ◇ q1) ◇ q1)) (cg (fun t => t ◇ q2) ((h q0 q0 q0).symm))).symm).trans ((h q1 ((q0 ◇ q0) ◇ q0) q2).symm)
  have apc1 : forall (q3 q4 q5:G), (q3 ◇ ((((q5 ◇ q3) ◇ q3) ◇ q4) ◇ q4)) = q4:=by
    intro q3 q4 q5
    exact ((cg (fun t => t ◇ ((((q5 ◇ q3) ◇ q3) ◇ q4) ◇ q4)) (apc0 q5 q3 q5)).symm).trans ((h q4 q5 ((q5 ◇ q3) ◇ q3)).symm)
  have apc4 : forall (q6 q7:G), (q7 ◇ (q6 ◇ ((q7 ◇ q6) ◇ q6))) = ((q7 ◇ q6) ◇ q6):=by
    intro q6 q7
    exact ((cg (fun t => q7 ◇ t) (cg (fun t => t ◇ ((q7 ◇ q6) ◇ q6)) ((h q6 q7 q7).symm))).symm).trans (apc1 q7 ((q7 ◇ q6) ◇ q6) q7)
  have apc5 : forall (q8 q9:G), ((q9 ◇ (q8 ◇ q9)) ◇ (q8 ◇ q9)) = (q9 ◇ (q8 ◇ q9)):=by
    intro q8 q9
    exact (((cg (fun t => q9 ◇ t) (apc0 q8 (q8 ◇ q9) q9)).symm).trans (apc4 (q8 ◇ q9) q9)).symm
  have apc7 : forall (q10 q11 q12:G), ((q11 ◇ q12) ◇ (q12 ◇ (q10 ◇ q12))) = (q10 ◇ q12):=by
    intro q10 q11 q12
    exact ((cg (fun t => (q11 ◇ q12) ◇ t) (apc5 q10 q12)).symm).trans (apc0 q11 (q10 ◇ q12) q12)
  have apc8 : forall (q13 q14 q15 q16:G), (((q16 ◇ q16) ◇ (q14 ◇ q15)) ◇ (q13 ◇ q15)) = (q15 ◇ (q13 ◇ q15)):=by
    intro q13 q14 q15 q16
    exact ((cg (fun t => ((q16 ◇ q16) ◇ (q14 ◇ q15)) ◇ t) (apc7 q13 q13 q15)).symm).trans (((cg (fun t => ((q16 ◇ q16) ◇ (q14 ◇ q15)) ◇ t) (cg (fun t => t ◇ (q15 ◇ (q13 ◇ q15))) (apc7 q13 q14 q15))).symm).trans ((h (q15 ◇ (q13 ◇ q15)) q16 (q14 ◇ q15)).symm))
  have apc10 : forall (q17 q18 q19:G), ((q19 ◇ q19) ◇ (q17 ◇ q18)) = (q18 ◇ (q17 ◇ q18)):=by
    intro q17 q18 q19
    exact ((cg (fun t => (q19 ◇ q19) ◇ t) (apc7 q17 q17 q18)).symm).trans ((((cg (fun t => (q19 ◇ q19) ◇ t) (cg (fun t => (q17 ◇ q18) ◇ t) (apc8 q17 q17 q18 q19))).symm).trans (apc4 (q17 ◇ q18) (q19 ◇ q19))).trans (apc8 q17 q17 q18 q19))
  have apc11 : forall (q20 q21:G), (q20 ◇ ((q21 ◇ q20) ◇ q20)) = q20:=by
    intro q20 q21
    exact ((apc10 (q21 ◇ q20) q20 q21).symm).trans (apc0 q21 q20 q21)
  have apc12 : forall (q6 q7 q20 q21:G), ((q7 ◇ q6) ◇ q6) = (q7 ◇ q6):=by
    intro q6 q7 q20 q21
    exact (((cg (fun t => q7 ◇ t) (apc11 q6 q7)).symm).trans (apc4 q6 q7)).symm
  have apc14 : forall (q22 q23 q24:G), (((q23 ◇ q23) ◇ q24) ◇ (q24 ◇ q22)) = q22:=by
    intro q22 q23 q24
    exact ((cg (fun t => ((q23 ◇ q23) ◇ q24) ◇ t) (apc12 q22 q24 q22 q22)).symm).trans ((h q22 q23 q24).symm)
  have apc16 : forall (q0 q1 q2 q6 q7 q20 q21:G), ((q0 ◇ q2) ◇ (q2 ◇ q1)) = q1:=by
    intro q0 q1 q2 q6 q7 q20 q21
    exact ((cg (fun t => (q0 ◇ q2) ◇ t) (apc12 q1 q2 ((q2 ◇ q1) ◇ q1) ((q2 ◇ q1) ◇ q1))).symm).trans (apc0 q0 q1 q2)
  have apc17 : forall (q25 q26 q27 q28:G), (q27 ◇ (q26 ◇ q25)) = q25:=by
    intro q25 q26 q27 q28
    exact (((cg (fun t => (q27 ◇ (q26 ◇ q25)) ◇ t) (apc12 q25 q26 ((q26 ◇ q25) ◇ q25) ((q26 ◇ q25) ◇ q25))).trans (apc12 (q26 ◇ q25) q27 ((q27 ◇ (q26 ◇ q25)) ◇ (q26 ◇ q25)) ((q27 ◇ (q26 ◇ q25)) ◇ (q26 ◇ q25)))).symm).trans ((((cg (fun t => (q27 ◇ (q26 ◇ q25)) ◇ t) (cg (fun t => (q26 ◇ q25) ◇ t) (apc14 q25 q28 q26))).symm).trans (apc7 ((q28 ◇ q28) ◇ q26) q27 (q26 ◇ q25))).trans (apc16 (q28 ◇ q28) q25 q26 (((q28 ◇ q28) ◇ q26) ◇ (q26 ◇ q25)) (((q28 ◇ q28) ◇ q26) ◇ (q26 ◇ q25)) (((q28 ◇ q28) ◇ q26) ◇ (q26 ◇ q25)) (((q28 ◇ q28) ◇ q26) ◇ (q26 ◇ q25))))
  exact (calc
    x = x:=rfl
    _ = (((y ◇ (z ◇ y)) ◇ x) ◇ (w ◇ x)):=((cg (fun t => t ◇ (w ◇ x)) (cg (fun t => t ◇ x) (apc17 y z y (y ◇ (z ◇ y))))).trans (apc17 x w (y ◇ x) ((y ◇ x) ◇ (w ◇ x)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_24451_to_28091 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_24451_to_28091
