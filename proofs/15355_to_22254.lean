-- Equation15355 → Equation22254
-- Recorded verdict: true
-- Premise: x = x * (((y * (z * x)) * z) * z)
-- Conclusion: x = (x * (x * y)) * ((x * y) * y)
-- Original submission SHA-256: 471e01584ce70b4fc9f34af1b28a45205bfaa52720397dc0cc5769b489505ec6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ (((y ◇ (z ◇ x)) ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ (x ◇ y)) ◇ ((x ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (x ◇ (((y ◇ (z ◇ x)) ◇ z) ◇ z)) = (x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (x y z:G), (x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ x)) = x:=by
    intro x y z
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2 : forall (q0 q1 q2:G), (q1 ◇ ((q2 ◇ ((q0 ◇ (q1 ◇ q2)) ◇ q1)) ◇ ((q0 ◇ (q1 ◇ q2)) ◇ q1))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ ((q0 ◇ (q1 ◇ q2)) ◇ q1)) (cg (fun t => t ◇ ((q0 ◇ (q1 ◇ q2)) ◇ q1)) ((h q2 q0 q1).symm)))).symm).trans ((h q1 q2 ((q0 ◇ (q1 ◇ q2)) ◇ q1)).symm)
  have apc3 : forall (q0 q3 q2 q4:G), ((((q0 ◇ (q3 ◇ q4)) ◇ q3) ◇ q3) ◇ (((q2 ◇ q4) ◇ q4) ◇ q4)) = (((q0 ◇ (q3 ◇ q4)) ◇ q3) ◇ q3):=by
    intro q0 q3 q2 q4
    exact ((cg (fun t => (((q0 ◇ (q3 ◇ q4)) ◇ q3) ◇ q3) ◇ t) (cg (fun t => t ◇ q4) (cg (fun t => t ◇ q4) (cg (fun t => q2 ◇ t) ((h q4 q0 q3).symm))))).symm).trans ((h (((q0 ◇ (q3 ◇ q4)) ◇ q3) ◇ q3) q2 q4).symm)
  have apc5 : forall (q5 q6 q7:G), ((((q5 ◇ (q6 ◇ (((q7 ◇ (q7 ◇ q7)) ◇ q7) ◇ q7))) ◇ q6) ◇ q6) ◇ q7) = (((q5 ◇ (q6 ◇ (((q7 ◇ (q7 ◇ q7)) ◇ q7) ◇ q7))) ◇ q6) ◇ q6):=by
    intro q5 q6 q7
    exact (((cg (fun t => (((q5 ◇ (q6 ◇ (((q7 ◇ (q7 ◇ q7)) ◇ q7) ◇ q7))) ◇ q6) ◇ q6) ◇ t) (cg (fun t => t ◇ (((q7 ◇ (q7 ◇ q7)) ◇ q7) ◇ q7)) (apc1 q7 (q7 ◇ (((q7 ◇ (q7 ◇ q7)) ◇ q7) ◇ q7)) (q7 ◇ (((q7 ◇ (q7 ◇ q7)) ◇ q7) ◇ q7))))).trans (cg (fun t => (((q5 ◇ (q6 ◇ (((q7 ◇ (q7 ◇ q7)) ◇ q7) ◇ q7))) ◇ q6) ◇ q6) ◇ t) (apc1 q7 (q7 ◇ (((q7 ◇ (q7 ◇ q7)) ◇ q7) ◇ q7)) (q7 ◇ (((q7 ◇ (q7 ◇ q7)) ◇ q7) ◇ q7))))).symm).trans (((cg (fun t => (((q5 ◇ (q6 ◇ (((q7 ◇ (q7 ◇ q7)) ◇ q7) ◇ q7))) ◇ q6) ◇ q6) ◇ t) (cg (fun t => t ◇ (((q7 ◇ (q7 ◇ q7)) ◇ q7) ◇ q7)) (cg (fun t => t ◇ (((q7 ◇ (q7 ◇ q7)) ◇ q7) ◇ q7)) (apc1 q7 q5 q5)))).symm).trans (apc3 q5 q6 q7 (((q7 ◇ (q7 ◇ q7)) ◇ q7) ◇ q7)))
  have apc6 : forall (q8 q9:G), ((((q8 ◇ q9) ◇ q9) ◇ q9) ◇ q9) = (((q8 ◇ q9) ◇ q9) ◇ q9):=by
    intro q8 q9
    exact (((cg (fun t => t ◇ q9) (cg (fun t => t ◇ q9) (cg (fun t => t ◇ q9) (cg (fun t => q8 ◇ t) ((h q9 q9 q9).symm))))).symm).trans (apc5 q8 q9 q9)).trans (cg (fun t => t ◇ q9) (cg (fun t => t ◇ q9) (cg (fun t => q8 ◇ t) (apc1 q9 (q9 ◇ (((q9 ◇ (q9 ◇ q9)) ◇ q9) ◇ q9)) (q9 ◇ (((q9 ◇ (q9 ◇ q9)) ◇ q9) ◇ q9))))))
  have apc8 : forall (q10 q11 q12:G), (q11 ◇ (((q10 ◇ ((q12 ◇ q11) ◇ (((q12 ◇ (q12 ◇ q12)) ◇ q12) ◇ q12))) ◇ (q12 ◇ q11)) ◇ (q12 ◇ q11))) = q11:=by
    intro q10 q11 q12
    exact ((cg (fun t => q11 ◇ t) (apc5 q10 (q12 ◇ q11) q12)).symm).trans (((cg (fun t => q11 ◇ t) (cg (fun t => t ◇ q12) (apc5 q10 (q12 ◇ q11) q12))).symm).trans ((h q11 ((q10 ◇ ((q12 ◇ q11) ◇ (((q12 ◇ (q12 ◇ q12)) ◇ q12) ◇ q12))) ◇ (q12 ◇ q11)) q12).symm))
  have apc11 : forall (q13 q14 q15:G), (q14 ◇ (((q15 ◇ (((q13 ◇ q14) ◇ q14) ◇ q14)) ◇ (((q13 ◇ q14) ◇ q14) ◇ q14)) ◇ (((q13 ◇ q14) ◇ q14) ◇ q14))) = q14:=by
    intro q13 q14 q15
    exact ((cg (fun t => q14 ◇ t) (cg (fun t => t ◇ (((q13 ◇ q14) ◇ q14) ◇ q14)) (cg (fun t => t ◇ (((q13 ◇ q14) ◇ q14) ◇ q14)) (cg (fun t => q15 ◇ t) (apc6 q13 q14))))).symm).trans ((h q14 q15 (((q13 ◇ q14) ◇ q14) ◇ q14)).symm)
  have apc13 : forall (q16 q17 q18 q19:G), (((q17 ◇ ((q16 ◇ (q19 ◇ q17)) ◇ q19)) ◇ ((q16 ◇ (q19 ◇ q17)) ◇ q19)) ◇ (((q18 ◇ q19) ◇ q19) ◇ q19)) = ((q17 ◇ ((q16 ◇ (q19 ◇ q17)) ◇ q19)) ◇ ((q16 ◇ (q19 ◇ q17)) ◇ q19)):=by
    intro q16 q17 q18 q19
    exact ((cg (fun t => ((q17 ◇ ((q16 ◇ (q19 ◇ q17)) ◇ q19)) ◇ ((q16 ◇ (q19 ◇ q17)) ◇ q19)) ◇ t) (cg (fun t => t ◇ q19) (cg (fun t => t ◇ q19) (cg (fun t => q18 ◇ t) (apc2 q16 q19 q17))))).symm).trans ((h ((q17 ◇ ((q16 ◇ (q19 ◇ q17)) ◇ q19)) ◇ ((q16 ◇ (q19 ◇ q17)) ◇ q19)) q18 q19).symm)
  have apc14 : forall (q20 q21 q22:G), (q20 ◇ (((q21 ◇ q22) ◇ q22) ◇ q22)) = q20:=by
    intro q20 q21 q22
    exact ((((cg (fun t => t ◇ (((q21 ◇ q22) ◇ q22) ◇ q22)) (cg (fun t => (q20 ◇ (((q20 ◇ ((q22 ◇ q20) ◇ (((q22 ◇ (q22 ◇ q22)) ◇ q22) ◇ q22))) ◇ (q22 ◇ q20)) ◇ (q22 ◇ q20))) ◇ t) (apc5 q20 (q22 ◇ q20) q22))).trans (cg (fun t => t ◇ (((q21 ◇ q22) ◇ q22) ◇ q22)) (cg (fun t => t ◇ (((q20 ◇ ((q22 ◇ q20) ◇ (((q22 ◇ (q22 ◇ q22)) ◇ q22) ◇ q22))) ◇ (q22 ◇ q20)) ◇ (q22 ◇ q20))) (apc8 q20 q20 q22)))).trans (cg (fun t => t ◇ (((q21 ◇ q22) ◇ q22) ◇ q22)) (apc8 q20 q20 q22))).symm).trans ((((cg (fun t => t ◇ (((q21 ◇ q22) ◇ q22) ◇ q22)) (cg (fun t => t ◇ ((((q20 ◇ ((q22 ◇ q20) ◇ (((q22 ◇ (q22 ◇ q22)) ◇ q22) ◇ q22))) ◇ (q22 ◇ q20)) ◇ (q22 ◇ q20)) ◇ q22)) (cg (fun t => q20 ◇ t) (apc5 q20 (q22 ◇ q20) q22)))).symm).trans (apc13 ((q20 ◇ ((q22 ◇ q20) ◇ (((q22 ◇ (q22 ◇ q22)) ◇ q22) ◇ q22))) ◇ (q22 ◇ q20)) q20 q21 q22)).trans ((((cg (fun t => t ◇ ((((q20 ◇ ((q22 ◇ q20) ◇ (((q22 ◇ (q22 ◇ q22)) ◇ q22) ◇ q22))) ◇ (q22 ◇ q20)) ◇ (q22 ◇ q20)) ◇ q22)) (cg (fun t => q20 ◇ t) (apc5 q20 (q22 ◇ q20) q22))).trans (cg (fun t => (q20 ◇ (((q20 ◇ ((q22 ◇ q20) ◇ (((q22 ◇ (q22 ◇ q22)) ◇ q22) ◇ q22))) ◇ (q22 ◇ q20)) ◇ (q22 ◇ q20))) ◇ t) (apc5 q20 (q22 ◇ q20) q22))).trans (cg (fun t => t ◇ (((q20 ◇ ((q22 ◇ q20) ◇ (((q22 ◇ (q22 ◇ q22)) ◇ q22) ◇ q22))) ◇ (q22 ◇ q20)) ◇ (q22 ◇ q20))) (apc8 q20 q20 q22))).trans (apc8 q20 q20 q22)))
  have apc15 : forall (q20 q21 q22 q13 q14 q15:G), (q14 ◇ q15) = q14:=by
    intro q20 q21 q22 q13 q14 q15
    exact ((((cg (fun t => q14 ◇ t) (cg (fun t => t ◇ (((q14 ◇ q14) ◇ q14) ◇ q14)) (cg (fun t => t ◇ (((q14 ◇ q14) ◇ q14) ◇ q14)) (apc14 q15 q14 q14)))).trans (cg (fun t => q14 ◇ t) (cg (fun t => t ◇ (((q14 ◇ q14) ◇ q14) ◇ q14)) (apc14 q15 q14 q14)))).trans (cg (fun t => q14 ◇ t) (apc14 q15 q14 q14))).symm).trans (apc11 q14 q14 q15)
  exact ((apc15 x x x x x (x ◇ y)).symm).trans ((apc15 x x x x (x ◇ (x ◇ y)) ((x ◇ y) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_15355_to_22254 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_15355_to_22254
