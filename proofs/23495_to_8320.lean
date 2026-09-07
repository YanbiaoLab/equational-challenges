-- Equation23495 → Equation8320
-- Recorded verdict: true
-- Premise: x = ((y ◇ y) ◇ x) ◇ (z ◇ (z ◇ y))
-- Conclusion: x = x ◇ (y ◇ (((y ◇ z) ◇ z) ◇ x))
-- Original submission SHA-256: 6245492fe2acce8fa46d2671a17ef0ff772929d7558903792d491763f89fbf81
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ x) ◇ (z ◇ (z ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (((y ◇ z) ◇ z) ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), ((q0 ◇ q0) ◇ (q2 ◇ (q2 ◇ (q0 ◇ q0)))) = (q1 ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q2 ◇ (q2 ◇ (q0 ◇ q0)))) ((h (q0 ◇ q0) q0 q1).symm)).symm).trans ((h (q1 ◇ (q1 ◇ q0)) (q0 ◇ q0) q2).symm)
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ (q1 ◇ q0)) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact ((apc0 q0 q1 q2).symm).trans (apc0 q0 q0 q2)
  have apc2 : forall (q3 q4:G), (((q4 ◇ q4) ◇ q3) ◇ (q4 ◇ (q4 ◇ q4))) = q3:=by
    intro q3 q4
    exact ((cg (fun t => ((q4 ◇ q4) ◇ q3) ◇ t) (apc1 q4 q3 q3)).symm).trans ((h q3 q4 q3).symm)
  have apc3 : forall (q5 q4 q6:G), ((q5 ◇ (q5 ◇ q5)) ◇ (q4 ◇ (q4 ◇ q4))) = ((q4 ◇ q4) ◇ q5):=by
    intro q5 q4 q6
    exact ((cg (fun t => (q5 ◇ (q5 ◇ q5)) ◇ t) (apc1 q4 q6 (q6 ◇ (q6 ◇ q4)))).symm).trans (((cg (fun t => t ◇ (q6 ◇ (q6 ◇ q4))) (apc1 q5 (q4 ◇ q4) q5)).symm).trans ((h ((q4 ◇ q4) ◇ q5) q4 q6).symm))
  have apc5 : forall (q7 q8 q9 q10:G), ((q7 ◇ (q7 ◇ q9)) ◇ (q9 ◇ (q9 ◇ q9))) = (q8 ◇ (q8 ◇ (q9 ◇ q9))):=by
    intro q7 q8 q9 q10
    exact ((cg (fun t => (q7 ◇ (q7 ◇ q9)) ◇ t) (apc1 q9 q10 (q10 ◇ (q10 ◇ q9)))).symm).trans (((cg (fun t => t ◇ (q10 ◇ (q10 ◇ q9))) (apc0 q9 q7 q8)).symm).trans ((h (q8 ◇ (q8 ◇ (q9 ◇ q9))) q9 q10).symm))
  have apc6 : forall (q11 q12:G), (q11 ◇ (q11 ◇ (q12 ◇ q12))) = ((q12 ◇ q12) ◇ q12):=by
    intro q11 q12
    exact ((apc5 (q12 ◇ q12) q11 q12 q11).symm).trans ((h ((q12 ◇ q12) ◇ q12) q12 q12).symm)
  have apc7 : forall (q13 q14:G), (q14 ◇ (q14 ◇ ((q13 ◇ q13) ◇ q13))) = q13:=by
    intro q13 q14
    exact (((cg (fun t => q14 ◇ t) (cg (fun t => q14 ◇ t) ((h ((q13 ◇ q13) ◇ q13) q13 (q13 ◇ q13)).symm))).symm).trans (apc6 q14 ((q13 ◇ q13) ◇ ((q13 ◇ q13) ◇ q13)))).trans (((((cg (fun t => t ◇ ((q13 ◇ q13) ◇ ((q13 ◇ q13) ◇ q13))) (cg (fun t => t ◇ ((q13 ◇ q13) ◇ ((q13 ◇ q13) ◇ q13))) (apc1 q13 (q13 ◇ q13) ((q13 ◇ q13) ◇ ((q13 ◇ q13) ◇ q13))))).trans (cg (fun t => t ◇ ((q13 ◇ q13) ◇ ((q13 ◇ q13) ◇ q13))) (cg (fun t => (q13 ◇ (q13 ◇ q13)) ◇ t) (apc1 q13 (q13 ◇ q13) ((q13 ◇ q13) ◇ ((q13 ◇ q13) ◇ q13)))))).trans (cg (fun t => ((q13 ◇ (q13 ◇ q13)) ◇ (q13 ◇ (q13 ◇ q13))) ◇ t) (apc1 q13 (q13 ◇ q13) ((q13 ◇ q13) ◇ ((q13 ◇ q13) ◇ q13))))).trans (cg (fun t => t ◇ (q13 ◇ (q13 ◇ q13))) (apc3 q13 q13 ((q13 ◇ (q13 ◇ q13)) ◇ (q13 ◇ (q13 ◇ q13)))))).trans (apc2 q13 q13))
  have apc9 : forall (q0 q15 q2:G), ((((q0 ◇ q0) ◇ q0) ◇ q15) ◇ (q2 ◇ (q2 ◇ (q0 ◇ (q0 ◇ q0))))) = q15:=by
    intro q0 q15 q2
    exact ((cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ q15) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (apc1 q0 (q0 ◇ q0) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))))).symm).trans (((cg (fun t => t ◇ (q2 ◇ (q2 ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))))) (cg (fun t => t ◇ q15) ((h ((q0 ◇ q0) ◇ q0) q0 (q0 ◇ q0)).symm))).symm).trans ((h q15 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) q2).symm))
  have apc10 : forall (q16 q17:G), ((((q16 ◇ q16) ◇ q16) ◇ q17) ◇ (q16 ◇ ((q16 ◇ q16) ◇ q16))) = q17:=by
    intro q16 q17
    exact ((cg (fun t => (((q16 ◇ q16) ◇ q16) ◇ q17) ◇ t) (cg (fun t => q16 ◇ t) (apc6 q16 q16))).symm).trans (apc9 q16 q17 q16)
  have apc11 : forall (q18 q19:G), (q18 ◇ (q18 ◇ q19)) = q19:=by
    intro q18 q19
    exact (((apc7 q19 q19).symm).trans (((cg (fun t => t ◇ (q19 ◇ ((q19 ◇ q19) ◇ q19))) ((h q19 q19 q18).symm)).symm).trans (apc10 q19 (q18 ◇ (q18 ◇ q19))))).symm
  have apc12 : forall (q20:G), ((q20 ◇ q20) ◇ q20) = q20:=by
    intro q20
    exact ((apc11 q20 ((q20 ◇ q20) ◇ q20)).symm).trans ((((cg (fun t => t ◇ (q20 ◇ ((q20 ◇ q20) ◇ q20))) (apc2 q20 q20)).symm).trans (apc10 q20 (q20 ◇ (q20 ◇ q20)))).trans (apc11 q20 q20))
  have apc13 : forall (q21 q22:G), (q21 ◇ q21) = q21:=by
    intro q21 q22
    exact ((cg (fun t => q21 ◇ t) (apc11 q22 q21)).symm).trans (((cg (fun t => t ◇ (q22 ◇ (q22 ◇ q21))) (apc12 q21)).symm).trans ((h q21 q21 q22).symm))
  have apc15 : forall (q20 q16 q17:G), ((q16 ◇ q17) ◇ q16) = q17:=by
    intro q20 q16 q17
    exact ((cg (fun t => (q16 ◇ q17) ◇ t) (apc13 q16 (q16 ◇ q16))).symm).trans ((((cg (fun t => t ◇ (q16 ◇ ((q16 ◇ q16) ◇ q16))) (cg (fun t => t ◇ q17) (apc12 q16))).trans (cg (fun t => (q16 ◇ q17) ◇ t) (cg (fun t => q16 ◇ t) (apc12 q16)))).symm).trans (apc10 q16 q17))
  have apc17 : forall (q23 q24:G), (q24 ◇ q23) = (q23 ◇ q24):=by
    intro q23 q24
    exact (((cg (fun t => t ◇ q24) (apc11 q24 q23)).symm).trans (apc15 q23 q24 (q24 ◇ q23))).symm
  have apc19 : forall (q0 q1 q15 q25:G), ((((q0 ◇ q1) ◇ q1) ◇ q15) ◇ q0) = q15:=by
    intro q0 q1 q15 q25
    exact (((((((((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q25) ◇ q25)) (cg (fun t => t ◇ q15) (cg (fun t => t ◇ (q1 ◇ (q1 ◇ q0))) (cg (fun t => q1 ◇ t) (apc17 q0 q1))))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q25) ◇ q25)) (cg (fun t => t ◇ q15) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => q1 ◇ t) (apc17 q0 q1)))))).trans (cg (fun t => (((q1 ◇ (q0 ◇ q1)) ◇ (q1 ◇ (q0 ◇ q1))) ◇ q15) ◇ t) (cg (fun t => t ◇ q25) (cg (fun t => t ◇ q25) (apc13 q0 (q0 ◇ q0)))))).trans (cg (fun t => t ◇ ((q0 ◇ q25) ◇ q25)) (cg (fun t => t ◇ q15) (cg (fun t => t ◇ (q1 ◇ (q0 ◇ q1))) (apc17 (q0 ◇ q1) q1))))).trans (cg (fun t => t ◇ ((q0 ◇ q25) ◇ q25)) (cg (fun t => t ◇ q15) (cg (fun t => ((q0 ◇ q1) ◇ q1) ◇ t) (apc17 (q0 ◇ q1) q1))))).trans (cg (fun t => ((((q0 ◇ q1) ◇ q1) ◇ ((q0 ◇ q1) ◇ q1)) ◇ q15) ◇ t) (cg (fun t => t ◇ q25) (apc17 q25 q0)))).trans (cg (fun t => t ◇ ((q25 ◇ q0) ◇ q25)) (cg (fun t => t ◇ q15) (apc13 ((q0 ◇ q1) ◇ q1) (((q0 ◇ q1) ◇ q1) ◇ ((q0 ◇ q1) ◇ q1)))))).trans (cg (fun t => (((q0 ◇ q1) ◇ q1) ◇ q15) ◇ t) (apc15 ((q25 ◇ q0) ◇ q25) q25 q0))).symm).trans (((cg (fun t => (((q1 ◇ (q1 ◇ q0)) ◇ (q1 ◇ (q1 ◇ q0))) ◇ q15) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q25) ◇ t) ((h q25 q0 q1).symm))).symm).trans ((h q15 (q1 ◇ (q1 ◇ q0)) ((q0 ◇ q0) ◇ q25)).symm))
  exact (calc
    x = x:=rfl
    _ = (x ◇ (y ◇ (((y ◇ z) ◇ z) ◇ x))):=(((cg (fun t => x ◇ t) (apc17 (((y ◇ z) ◇ z) ◇ x) y)).trans (cg (fun t => x ◇ t) (apc19 y z x ((((y ◇ z) ◇ z) ◇ x) ◇ y)))).trans (apc13 x (x ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23495_to_8320 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_23495_to_8320
