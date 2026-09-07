-- Equation13556 → Equation1047
-- Recorded verdict: true
-- Premise: x = x * ((y * ((y * x) * x)) * z)
-- Conclusion: x = x * ((y * (y * x)) * z)
-- Original submission SHA-256: 53214b96ace6c15415ef58d3fd9b47750b979a3a04ef008a0744169d8daecb2f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ ((y ◇ ((y ◇ x) ◇ x)) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ ((y ◇ (y ◇ x)) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), (q0 ◇ (q1 ◇ ((q1 ◇ q0) ◇ q0))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => q0 ◇ t) ((h (q1 ◇ ((q1 ◇ q0) ◇ q0)) q0 q0).symm)).symm).trans ((h q0 q1 ((q0 ◇ ((q0 ◇ (q1 ◇ ((q1 ◇ q0) ◇ q0))) ◇ (q1 ◇ ((q1 ◇ q0) ◇ q0)))) ◇ q0)).symm)
  have apc1 : forall (x y z:G), (x ◇ ((y ◇ ((y ◇ x) ◇ x)) ◇ z)) = (x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc2 : forall (q2:G), (q2 ◇ ((q2 ◇ ((q2 ◇ q2) ◇ q2)) ◇ q2)) = q2:=by
    intro q2
    exact ((apc1 q2 q2 q2).symm).trans ((h q2 q2 q2).symm)
  have apc3 : forall (q1 q3:G), (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ q3)) = ((q1 ◇ q1) ◇ q1):=by
    intro q1 q3
    exact ((cg (fun t => ((q1 ◇ q1) ◇ q1) ◇ t) (cg (fun t => t ◇ q3) ((h q1 q1 ((q1 ◇ q1) ◇ q1)).symm))).symm).trans ((h ((q1 ◇ q1) ◇ q1) q1 q3).symm)
  have apc4 : forall (q4 q5:G), ((q4 ◇ ((q4 ◇ q5) ◇ q5)) ◇ (q5 ◇ q5)) = (q4 ◇ ((q4 ◇ q5) ◇ q5)):=by
    intro q4 q5
    exact ((cg (fun t => (q4 ◇ ((q4 ◇ q5) ◇ q5)) ◇ t) (cg (fun t => q5 ◇ t) (apc0 q5 q4))).symm).trans (((cg (fun t => (q4 ◇ ((q4 ◇ q5) ◇ q5)) ◇ t) (cg (fun t => q5 ◇ t) (cg (fun t => t ◇ (q4 ◇ ((q4 ◇ q5) ◇ q5))) (apc0 q5 q4)))).symm).trans (apc0 (q4 ◇ ((q4 ◇ q5) ◇ q5)) q5))
  have apc6 : forall (q6 q7 q8:G), ((q6 ◇ q7) ◇ ((((q6 ◇ q6) ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) ◇ q8)) = (q6 ◇ q7):=by
    intro q6 q7 q8
    exact ((cg (fun t => (q6 ◇ q7) ◇ t) (cg (fun t => t ◇ q8) (cg (fun t => ((q6 ◇ q6) ◇ q6) ◇ t) (apc3 q6 q7)))).symm).trans (((cg (fun t => (q6 ◇ q7) ◇ t) (cg (fun t => t ◇ q8) (cg (fun t => ((q6 ◇ q6) ◇ q6) ◇ t) (cg (fun t => t ◇ (q6 ◇ q7)) (apc3 q6 q7))))).symm).trans ((h (q6 ◇ q7) ((q6 ◇ q6) ◇ q6) q8).symm))
  have apc7 : forall (q9 q10:G), (q9 ◇ ((((q9 ◇ q9) ◇ q9) ◇ ((q9 ◇ q9) ◇ q9)) ◇ q10)) = q9:=by
    intro q9 q10
    exact (((cg (fun t => t ◇ ((((q9 ◇ q9) ◇ q9) ◇ ((q9 ◇ q9) ◇ q9)) ◇ q10)) (apc2 q9)).symm).trans (apc6 q9 ((q9 ◇ ((q9 ◇ q9) ◇ q9)) ◇ q9) q10)).trans (apc2 q9)
  have apc8 : forall (q11:G), (q11 ◇ (((q11 ◇ q11) ◇ q11) ◇ ((q11 ◇ q11) ◇ q11))) = q11:=by
    intro q11
    exact ((cg (fun t => q11 ◇ t) ((h (((q11 ◇ q11) ◇ q11) ◇ ((q11 ◇ q11) ◇ q11)) q11 q11).symm)).symm).trans (apc7 q11 ((q11 ◇ ((q11 ◇ (((q11 ◇ q11) ◇ q11) ◇ ((q11 ◇ q11) ◇ q11))) ◇ (((q11 ◇ q11) ◇ q11) ◇ ((q11 ◇ q11) ◇ q11)))) ◇ q11))
  have apc9 : forall (q12:G), (((q12 ◇ q12) ◇ q12) ◇ q12) = ((q12 ◇ q12) ◇ q12):=by
    intro q12
    exact ((cg (fun t => ((q12 ◇ q12) ◇ q12) ◇ t) ((h q12 q12 ((q12 ◇ q12) ◇ q12)).symm)).symm).trans (apc0 ((q12 ◇ q12) ◇ q12) q12)
  have apc12 : forall (q13 q14 q15:G), ((q13 ◇ ((q13 ◇ q14) ◇ q14)) ◇ ((q14 ◇ q14) ◇ q15)) = (q13 ◇ ((q13 ◇ q14) ◇ q14)):=by
    intro q13 q14 q15
    exact ((cg (fun t => (q13 ◇ ((q13 ◇ q14) ◇ q14)) ◇ t) (cg (fun t => t ◇ q15) (cg (fun t => q14 ◇ t) (apc0 q14 q13)))).symm).trans (((cg (fun t => (q13 ◇ ((q13 ◇ q14) ◇ q14)) ◇ t) (cg (fun t => t ◇ q15) (cg (fun t => q14 ◇ t) (cg (fun t => t ◇ (q13 ◇ ((q13 ◇ q14) ◇ q14))) (apc0 q14 q13))))).symm).trans ((h (q13 ◇ ((q13 ◇ q14) ◇ q14)) q14 q15).symm))
  have apc15 : forall (q16 q17:G), ((q16 ◇ q17) ◇ (((q16 ◇ q16) ◇ q16) ◇ ((q16 ◇ q16) ◇ q16))) = (q16 ◇ q17):=by
    intro q16 q17
    exact ((cg (fun t => (q16 ◇ q17) ◇ t) (cg (fun t => ((q16 ◇ q16) ◇ q16) ◇ t) (apc3 q16 q17))).symm).trans (((cg (fun t => (q16 ◇ q17) ◇ t) (cg (fun t => ((q16 ◇ q16) ◇ q16) ◇ t) (cg (fun t => t ◇ (q16 ◇ q17)) (apc3 q16 q17)))).symm).trans (apc0 (q16 ◇ q17) ((q16 ◇ q16) ◇ q16)))
  have apc17 : forall (q18 q19 q20:G), ((q19 ◇ q19) ◇ (((q18 ◇ ((q18 ◇ q19) ◇ q19)) ◇ (q18 ◇ ((q18 ◇ q19) ◇ q19))) ◇ q20)) = (q19 ◇ q19):=by
    intro q18 q19 q20
    exact ((cg (fun t => (q19 ◇ q19) ◇ t) (cg (fun t => t ◇ q20) (cg (fun t => (q18 ◇ ((q18 ◇ q19) ◇ q19)) ◇ t) (apc4 q18 q19)))).symm).trans (((cg (fun t => (q19 ◇ q19) ◇ t) (cg (fun t => t ◇ q20) (cg (fun t => (q18 ◇ ((q18 ◇ q19) ◇ q19)) ◇ t) (cg (fun t => t ◇ (q19 ◇ q19)) (apc4 q18 q19))))).symm).trans ((h (q19 ◇ q19) (q18 ◇ ((q18 ◇ q19) ◇ q19)) q20).symm))
  have apc18 : forall (q21 q22:G), ((q21 ◇ q21) ◇ (((q21 ◇ q21) ◇ ((q21 ◇ q21) ◇ q21)) ◇ q22)) = (q21 ◇ q21):=by
    intro q21 q22
    exact ((cg (fun t => (q21 ◇ q21) ◇ t) (cg (fun t => t ◇ q22) (cg (fun t => (q21 ◇ q21) ◇ t) (apc9 q21)))).symm).trans (((cg (fun t => (q21 ◇ q21) ◇ t) (cg (fun t => t ◇ q22) (apc12 (q21 ◇ q21) q21 (((q21 ◇ q21) ◇ q21) ◇ q21)))).symm).trans (apc17 (q21 ◇ q21) q21 q22))
  have apc19 : forall (q23 q24:G), (((q23 ◇ q23) ◇ q23) ◇ ((q23 ◇ q23) ◇ q24)) = ((q23 ◇ q23) ◇ q23):=by
    intro q23 q24
    exact ((cg (fun t => ((q23 ◇ q23) ◇ q23) ◇ t) (cg (fun t => t ◇ q24) (apc18 q23 ((q23 ◇ q23) ◇ q23)))).symm).trans ((h ((q23 ◇ q23) ◇ q23) (q23 ◇ q23) q24).symm)
  have apc20 : forall (q11 q23 q24:G), (q11 ◇ ((q11 ◇ q11) ◇ q11)) = q11:=by
    intro q11 q23 q24
    exact ((cg (fun t => q11 ◇ t) (apc19 q11 q11)).symm).trans (apc8 q11)
  have apc25 : forall (q25:G), (q25 ◇ q25) = q25:=by
    intro q25
    exact ((cg (fun t => q25 ◇ t) (apc20 q25 q25 q25)).symm).trans (apc0 q25 q25)
  have apc26 : forall (q23 q24 q16 q17:G), ((q16 ◇ q17) ◇ q16) = (q16 ◇ q17):=by
    intro q23 q24 q16 q17
    exact (((cg (fun t => (q16 ◇ q17) ◇ t) (cg (fun t => t ◇ q16) (apc25 q16))).trans (cg (fun t => (q16 ◇ q17) ◇ t) (apc25 q16))).symm).trans (((cg (fun t => (q16 ◇ q17) ◇ t) (apc19 q16 q16)).symm).trans (apc15 q16 q17))
  have apc27 : forall (q26 q27 q28:G), (q27 ◇ ((q27 ◇ q26) ◇ q28)) = q27:=by
    intro q26 q27 q28
    exact (((cg (fun t => q27 ◇ t) (cg (fun t => t ◇ q28) (cg (fun t => (q27 ◇ q26) ◇ t) (apc26 ((q27 ◇ q26) ◇ q27) ((q27 ◇ q26) ◇ q27) q27 q26)))).trans (cg (fun t => q27 ◇ t) (cg (fun t => t ◇ q28) (apc25 (q27 ◇ q26))))).symm).trans (((cg (fun t => q27 ◇ t) (cg (fun t => t ◇ q28) (cg (fun t => (q27 ◇ q26) ◇ t) (cg (fun t => t ◇ q27) (apc26 q26 q26 q27 q26))))).symm).trans ((h q27 (q27 ◇ q26) q28).symm))
  have apc29 : forall (q0 q1 q26 q27 q28:G), (q0 ◇ q1) = q0:=by
    intro q0 q1 q26 q27 q28
    exact ((cg (fun t => q0 ◇ t) (apc27 q0 q1 q0)).symm).trans (apc0 q0 q1)
  exact (apc29 x ((y ◇ (y ◇ x)) ◇ z) x x x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_13556_to_1047 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_13556_to_1047
