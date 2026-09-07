-- Equation23773 → Equation17972
-- Recorded verdict: true
-- Premise: x = ((y ◇ z) ◇ z) ◇ (x ◇ (x ◇ z))
-- Conclusion: x = (x ◇ y) ◇ (y ◇ ((z ◇ w) ◇ y))
-- Original submission SHA-256: 8dadcda7b0e523e50662d8bc14fbb99dbeb3a2356ac191c19410fe937045fa91
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ z) ◇ (x ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ y) ◇ (y ◇ ((z ◇ w) ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc3 : forall (q0 q1 q2:G), (((q2 ◇ (((q0 ◇ q1) ◇ q1) ◇ q1)) ◇ (((q0 ◇ q1) ◇ q1) ◇ q1)) ◇ ((q0 ◇ q1) ◇ q1)) = ((q0 ◇ q1) ◇ q1):=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q2 ◇ (((q0 ◇ q1) ◇ q1) ◇ q1)) ◇ (((q0 ◇ q1) ◇ q1) ◇ q1)) ◇ t) ((h ((q0 ◇ q1) ◇ q1) q0 q1).symm)).symm).trans ((h ((q0 ◇ q1) ◇ q1) q2 (((q0 ◇ q1) ◇ q1) ◇ q1)).symm)
  have apc4 : forall (q3 q0 q1 q2:G), (((q2 ◇ (q3 ◇ (q3 ◇ q1))) ◇ (q3 ◇ (q3 ◇ q1))) ◇ (((q0 ◇ q1) ◇ q1) ◇ q3)) = ((q0 ◇ q1) ◇ q1):=by
    intro q3 q0 q1 q2
    exact ((cg (fun t => ((q2 ◇ (q3 ◇ (q3 ◇ q1))) ◇ (q3 ◇ (q3 ◇ q1))) ◇ t) (cg (fun t => ((q0 ◇ q1) ◇ q1) ◇ t) ((h q3 q0 q1).symm))).symm).trans ((h ((q0 ◇ q1) ◇ q1) q2 (q3 ◇ (q3 ◇ q1))).symm)
  have apc6 : forall (q4 q5:G), ((((q4 ◇ q5) ◇ q5) ◇ (((q4 ◇ q5) ◇ q5) ◇ q5)) ◇ ((q4 ◇ q5) ◇ q5)) = ((q4 ◇ q5) ◇ q5):=by
    intro q4 q5
    exact ((cg (fun t => t ◇ ((q4 ◇ q5) ◇ q5)) (cg (fun t => t ◇ (((q4 ◇ q5) ◇ q5) ◇ q5)) (apc4 q5 q4 q5 q4))).symm).trans (apc3 q4 q5 ((q4 ◇ (q5 ◇ (q5 ◇ q5))) ◇ (q5 ◇ (q5 ◇ q5))))
  have apc7 : forall (q6 q7 q8:G), ((((q6 ◇ q7) ◇ q7) ◇ ((q6 ◇ q7) ◇ q7)) ◇ (q8 ◇ (q8 ◇ ((q6 ◇ q7) ◇ q7)))) = q8:=by
    intro q6 q7 q8
    exact ((cg (fun t => t ◇ (q8 ◇ (q8 ◇ ((q6 ◇ q7) ◇ q7)))) (cg (fun t => t ◇ ((q6 ◇ q7) ◇ q7)) (apc3 q6 q7 q6))).symm).trans ((h q8 ((q6 ◇ (((q6 ◇ q7) ◇ q7) ◇ q7)) ◇ (((q6 ◇ q7) ◇ q7) ◇ q7)) ((q6 ◇ q7) ◇ q7)).symm)
  have apc8 : forall (q9 q10:G), ((((q9 ◇ q10) ◇ q10) ◇ ((q9 ◇ q10) ◇ q10)) ◇ ((q9 ◇ q10) ◇ q10)) = (((q9 ◇ q10) ◇ q10) ◇ (((q9 ◇ q10) ◇ q10) ◇ q10)):=by
    intro q9 q10
    exact ((cg (fun t => (((q9 ◇ q10) ◇ q10) ◇ ((q9 ◇ q10) ◇ q10)) ◇ t) (apc6 q9 q10)).symm).trans (((cg (fun t => (((q9 ◇ q10) ◇ q10) ◇ ((q9 ◇ q10) ◇ q10)) ◇ t) (cg (fun t => (((q9 ◇ q10) ◇ q10) ◇ (((q9 ◇ q10) ◇ q10) ◇ q10)) ◇ t) (apc6 q9 q10))).symm).trans (apc7 q9 q10 (((q9 ◇ q10) ◇ q10) ◇ (((q9 ◇ q10) ◇ q10) ◇ q10))))
  have apc9 : forall (q11 q12:G), ((((q11 ◇ q12) ◇ q12) ◇ q12) ◇ ((q11 ◇ q12) ◇ q12)) = ((q11 ◇ q12) ◇ q12):=by
    intro q11 q12
    exact ((cg (fun t => t ◇ ((q11 ◇ q12) ◇ q12)) (apc6 (q11 ◇ q12) q12)).symm).trans (((cg (fun t => t ◇ ((q11 ◇ q12) ◇ q12)) (cg (fun t => t ◇ (((q11 ◇ q12) ◇ q12) ◇ q12)) (apc8 (q11 ◇ q12) q12))).symm).trans (apc3 q11 q12 ((((q11 ◇ q12) ◇ q12) ◇ q12) ◇ (((q11 ◇ q12) ◇ q12) ◇ q12))))
  have apc10 : forall (q13 q14:G), (((q13 ◇ q14) ◇ q14) ◇ (((q13 ◇ q14) ◇ q14) ◇ q14)) = ((q13 ◇ q14) ◇ q14):=by
    intro q13 q14
    exact (((((cg (fun t => (((((q13 ◇ q14) ◇ q14) ◇ (((q13 ◇ q14) ◇ q14) ◇ q14)) ◇ ((q13 ◇ q14) ◇ q14)) ◇ ((q13 ◇ q14) ◇ q14)) ◇ t) (cg (fun t => t ◇ ((q13 ◇ q14) ◇ q14)) (apc8 q13 q14))).trans (cg (fun t => t ◇ ((((q13 ◇ q14) ◇ q14) ◇ (((q13 ◇ q14) ◇ q14) ◇ q14)) ◇ ((q13 ◇ q14) ◇ q14))) (cg (fun t => t ◇ ((q13 ◇ q14) ◇ q14)) (apc6 q13 q14)))).trans (cg (fun t => (((q13 ◇ q14) ◇ q14) ◇ ((q13 ◇ q14) ◇ q14)) ◇ t) (apc6 q13 q14))).trans (apc8 q13 q14)).symm).trans ((((cg (fun t => t ◇ (((((q13 ◇ q14) ◇ q14) ◇ ((q13 ◇ q14) ◇ q14)) ◇ ((q13 ◇ q14) ◇ q14)) ◇ ((q13 ◇ q14) ◇ q14))) (cg (fun t => t ◇ ((q13 ◇ q14) ◇ q14)) (cg (fun t => t ◇ ((q13 ◇ q14) ◇ q14)) (apc8 q13 q14)))).symm).trans (apc9 (((q13 ◇ q14) ◇ q14) ◇ ((q13 ◇ q14) ◇ q14)) ((q13 ◇ q14) ◇ q14))).trans ((cg (fun t => t ◇ ((q13 ◇ q14) ◇ q14)) (apc8 q13 q14)).trans (apc6 q13 q14)))
  have apc11 : forall (q4 q5:G), (((q4 ◇ q5) ◇ q5) ◇ ((q4 ◇ q5) ◇ q5)) = ((q4 ◇ q5) ◇ q5):=by
    intro q4 q5
    exact ((cg (fun t => t ◇ ((q4 ◇ q5) ◇ q5)) (apc10 q4 q5)).symm).trans (apc6 q4 q5)
  have apc12 : forall (q15 q16:G), (((q15 ◇ q16) ◇ q16) ◇ q16) = ((q15 ◇ q16) ◇ q16):=by
    intro q15 q16
    exact (((((cg (fun t => t ◇ ((((q15 ◇ q16) ◇ q16) ◇ q16) ◇ ((q15 ◇ q16) ◇ q16))) (apc11 q15 q16)).trans (cg (fun t => ((q15 ◇ q16) ◇ q16) ◇ t) (apc9 q15 q16))).trans (apc11 q15 q16)).symm).trans (((cg (fun t => (((q15 ◇ q16) ◇ q16) ◇ ((q15 ◇ q16) ◇ q16)) ◇ t) (cg (fun t => (((q15 ◇ q16) ◇ q16) ◇ q16) ◇ t) (apc9 q15 q16))).symm).trans (apc7 q15 q16 (((q15 ◇ q16) ◇ q16) ◇ q16)))).symm
  have apc13 : forall (q0 q1 q2:G), ((q2 ◇ ((q0 ◇ q1) ◇ q1)) ◇ ((q0 ◇ q1) ◇ q1)) = ((q0 ◇ q1) ◇ q1):=by
    intro q0 q1 q2
    exact ((((cg (fun t => t ◇ ((q0 ◇ q1) ◇ q1)) (cg (fun t => t ◇ (((q0 ◇ q1) ◇ q1) ◇ q1)) (cg (fun t => q2 ◇ t) (apc12 q0 q1)))).trans (cg (fun t => t ◇ ((q0 ◇ q1) ◇ q1)) (cg (fun t => (q2 ◇ ((q0 ◇ q1) ◇ q1)) ◇ t) (apc12 q0 q1)))).trans (apc12 q2 ((q0 ◇ q1) ◇ q1))).symm).trans (apc3 q0 q1 q2)
  have apc14 : forall (q17 q18 q19 q20:G), (q19 ◇ ((q17 ◇ q18) ◇ q18)) = ((q17 ◇ q18) ◇ q18):=by
    intro q17 q18 q19 q20
    exact (((((cg (fun t => ((q20 ◇ ((q17 ◇ q18) ◇ q18)) ◇ ((q17 ◇ q18) ◇ q18)) ◇ t) (apc13 q17 q18 q19)).trans (cg (fun t => t ◇ ((q17 ◇ q18) ◇ q18)) (apc13 q17 q18 q20))).trans (apc11 q17 q18)).symm).trans (((cg (fun t => ((q20 ◇ ((q17 ◇ q18) ◇ q18)) ◇ ((q17 ◇ q18) ◇ q18)) ◇ t) (cg (fun t => (q19 ◇ ((q17 ◇ q18) ◇ q18)) ◇ t) (apc13 q17 q18 q19))).symm).trans ((h (q19 ◇ ((q17 ◇ q18) ◇ q18)) q20 ((q17 ◇ q18) ◇ q18)).symm))).symm
  have apc15 : forall (q21 q22 q23:G), ((q21 ◇ q22) ◇ q22) = q23:=by
    intro q21 q22 q23
    exact ((((cg (fun t => ((q21 ◇ q22) ◇ q22) ◇ t) (cg (fun t => q23 ◇ t) (apc14 q21 q22 q23 (q23 ◇ ((q21 ◇ q22) ◇ q22))))).trans (cg (fun t => ((q21 ◇ q22) ◇ q22) ◇ t) (apc14 q21 q22 q23 (q23 ◇ ((q21 ◇ q22) ◇ q22))))).trans (apc14 q21 q22 ((q21 ◇ q22) ◇ q22) (((q21 ◇ q22) ◇ q22) ◇ ((q21 ◇ q22) ◇ q22)))).symm).trans (((cg (fun t => t ◇ (q23 ◇ (q23 ◇ ((q21 ◇ q22) ◇ q22)))) (apc14 q21 q22 (q21 ◇ ((q21 ◇ q22) ◇ q22)) q21)).symm).trans ((h q23 q21 ((q21 ◇ q22) ◇ q22)).symm))
  exact ((apc15 ((x ◇ y) ◇ (y ◇ ((z ◇ w) ◇ y))) x x).symm).trans (apc15 ((x ◇ y) ◇ (y ◇ ((z ◇ w) ◇ y))) x ((x ◇ y) ◇ (y ◇ ((z ◇ w) ◇ y))))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23773_to_17972 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_23773_to_17972
