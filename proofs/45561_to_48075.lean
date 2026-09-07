-- Equation45561 → Equation48075
-- Recorded verdict: true
-- Premise: x * y = z * (((x * y) * x) * z)
-- Conclusion: x * y = (y * (y * y)) * (z * x)
-- Original submission SHA-256: e95caff1aa88bf5905096628f83b10527ddd7fb94c586b0f973faff06cecbe87
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ (((x ◇ y) ◇ x) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ (y ◇ y)) ◇ (z ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 q3:G), ((((q0 ◇ q1) ◇ q0) ◇ ((q2 ◇ q3) ◇ q2)) ◇ (q0 ◇ q1)) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (((q0 ◇ q1) ◇ q0) ◇ ((q2 ◇ q3) ◇ q2)) ◇ t) ((h q0 q1 ((q2 ◇ q3) ◇ q2)).symm)).symm).trans ((h q2 q3 (((q0 ◇ q1) ◇ q0) ◇ ((q2 ◇ q3) ◇ q2))).symm)
  have apc1 : forall (q4 q5:G), ((q4 ◇ q5) ◇ (((q4 ◇ q5) ◇ q4) ◇ (q4 ◇ q5))) = (q4 ◇ q5):=by
    intro q4 q5
    exact ((cg (fun t => t ◇ (((q4 ◇ q5) ◇ q4) ◇ (q4 ◇ q5))) (apc0 (q4 ◇ q5) q4 q4 q5)).symm).trans (apc0 ((q4 ◇ q5) ◇ q4) (q4 ◇ q5) q4 q5)
  have apc2 : forall (q6 q7 q8:G), (q8 ◇ (((q6 ◇ q7) ◇ (q6 ◇ q7)) ◇ q8)) = (q6 ◇ q7):=by
    intro q6 q7 q8
    exact (((cg (fun t => q8 ◇ t) (cg (fun t => t ◇ q8) (cg (fun t => t ◇ (q6 ◇ q7)) (apc1 q6 q7)))).symm).trans ((h (q6 ◇ q7) (((q6 ◇ q7) ◇ q6) ◇ (q6 ◇ q7)) q8).symm)).trans (apc1 q6 q7)
  have apc3 : forall (q9 q10:G), ((q10 ◇ q9) ◇ (q10 ◇ q9)) = ((q10 ◇ q9) ◇ q10):=by
    intro q9 q10
    exact ((cg (fun t => (q10 ◇ q9) ◇ t) (apc0 q10 q9 q10 q9)).symm).trans (apc2 (q10 ◇ q9) q10 (q10 ◇ q9))
  have apc4 : forall (q11 q12:G), ((((q11 ◇ q12) ◇ q11) ◇ (q11 ◇ q12)) ◇ (q11 ◇ q12)) = (q11 ◇ q12):=by
    intro q11 q12
    exact ((cg (fun t => t ◇ (q11 ◇ q12)) (apc3 q11 (q11 ◇ q12))).symm).trans (apc0 q11 q12 q11 q12)
  have apc5 : forall (x y z:G), (z ◇ (((x ◇ y) ◇ x) ◇ z)) = (x ◇ (((x ◇ y) ◇ x) ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc6 : forall (q13 q14:G), (q13 ◇ (((q13 ◇ q14) ◇ q13) ◇ q13)) = ((q13 ◇ q14) ◇ q13):=by
    intro q13 q14
    exact ((((cg (fun t => (q13 ◇ q14) ◇ t) (apc4 q13 q14)).trans (apc3 q14 q13)).symm).trans ((((cg (fun t => t ◇ ((((q13 ◇ q14) ◇ q13) ◇ (q13 ◇ q14)) ◇ (q13 ◇ q14))) (apc4 q13 q14)).symm).trans (apc3 (q13 ◇ q14) (((q13 ◇ q14) ◇ q13) ◇ (q13 ◇ q14)))).trans ((cg (fun t => t ◇ (((q13 ◇ q14) ◇ q13) ◇ (q13 ◇ q14))) (apc4 q13 q14)).trans (apc5 q13 q14 (q13 ◇ q14))))).symm
  have apc7 : forall (q15 q16:G), ((q15 ◇ q16) ◇ q15) = (q15 ◇ q16):=by
    intro q15 q16
    exact ((apc6 q15 q16).symm).trans ((h q15 q16 q15).symm)
  have apc8 : forall (q0 q1 q2 q3 q15 q16:G), ((q0 ◇ q1) ◇ (q2 ◇ q3)) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3 q15 q16
    exact ((((cg (fun t => t ◇ (q0 ◇ q1)) (cg (fun t => t ◇ ((q2 ◇ q3) ◇ q2)) (apc7 q0 q1))).trans (cg (fun t => t ◇ (q0 ◇ q1)) (cg (fun t => (q0 ◇ q1) ◇ t) (apc7 q2 q3)))).trans (apc7 (q0 ◇ q1) (q2 ◇ q3))).symm).trans (apc0 q0 q1 q2 q3)
  have apc10 : forall (q17 q18 q19:G), ((q17 ◇ q18) ◇ q19) = (q17 ◇ q18):=by
    intro q17 q18 q19
    exact (((apc8 (q17 ◇ q18) q19 q17 q18 q17 q17).symm).trans (apc7 (q17 ◇ q18) q19)).symm
  have apc13 : forall (q20 q21 q22 q23:G), (q22 ◇ q23) = (q20 ◇ q21):=by
    intro q20 q21 q22 q23
    exact (((((((cg (fun t => t ◇ (q22 ◇ q23)) (cg (fun t => ((q22 ◇ q23) ◇ q22) ◇ t) (cg (fun t => (q20 ◇ q21) ◇ t) (cg (fun t => t ◇ (q20 ◇ q21)) (apc10 q20 q21 q20))))).trans (cg (fun t => t ◇ (q22 ◇ q23)) (cg (fun t => ((q22 ◇ q23) ◇ q22) ◇ t) (cg (fun t => (q20 ◇ q21) ◇ t) (apc10 q20 q21 (q20 ◇ q21)))))).trans (cg (fun t => t ◇ (q22 ◇ q23)) (cg (fun t => t ◇ ((q20 ◇ q21) ◇ (q20 ◇ q21))) (apc10 q22 q23 q22)))).trans (cg (fun t => t ◇ (q22 ◇ q23)) (cg (fun t => (q22 ◇ q23) ◇ t) (apc10 q20 q21 (q20 ◇ q21))))).trans (cg (fun t => t ◇ (q22 ◇ q23)) (apc10 q22 q23 (q20 ◇ q21)))).trans (apc10 q22 q23 (q22 ◇ q23))).symm).trans ((((cg (fun t => t ◇ (q22 ◇ q23)) (cg (fun t => ((q22 ◇ q23) ◇ q22) ◇ t) (cg (fun t => t ◇ (((q20 ◇ q21) ◇ q20) ◇ (q20 ◇ q21))) (apc4 q20 q21)))).symm).trans (apc0 q22 q23 (((q20 ◇ q21) ◇ q20) ◇ (q20 ◇ q21)) (q20 ◇ q21))).trans (((cg (fun t => t ◇ (q20 ◇ q21)) (cg (fun t => t ◇ (q20 ◇ q21)) (apc10 q20 q21 q20))).trans (cg (fun t => t ◇ (q20 ◇ q21)) (apc10 q20 q21 (q20 ◇ q21)))).trans (apc10 q20 q21 (q20 ◇ q21))))
  exact (apc13 (x ◇ y) ((y ◇ (y ◇ y)) ◇ (z ◇ x)) x y).trans ((apc13 (x ◇ y) ((y ◇ (y ◇ y)) ◇ (z ◇ x)) (y ◇ (y ◇ y)) (z ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45561_to_48075 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45561_to_48075
