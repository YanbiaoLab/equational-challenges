-- Equation15632 → Equation38679
-- Recorded verdict: true
-- Premise: x = y ◇ (((y ◇ (y ◇ z)) ◇ x) ◇ z)
-- Conclusion: x = ((y ◇ ((z ◇ y) ◇ w)) ◇ u) ◇ v
-- Original submission SHA-256: 953f140e67a52d83e615ae283d12fbe38ad7dafaaf37db23d4f1778133c6bfdb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (((y ◇ (y ◇ z)) ◇ x) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x = ((y ◇ ((z ◇ y) ◇ w)) ◇ u) ◇ v
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 q3:G), ((((q2 ◇ (q2 ◇ q3)) ◇ ((q2 ◇ (q2 ◇ q3)) ◇ q1)) ◇ q0) ◇ q1) = (q2 ◇ (q0 ◇ q3)):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q3) ((h q0 (q2 ◇ (q2 ◇ q3)) q1).symm))).symm).trans ((h ((((q2 ◇ (q2 ◇ q3)) ◇ ((q2 ◇ (q2 ◇ q3)) ◇ q1)) ◇ q0) ◇ q1) q2 q3).symm)).symm
  have apc1 : forall (q4 q5 q6:G), ((q4 ◇ (q4 ◇ q5)) ◇ (q4 ◇ (q6 ◇ q5))) = q6:=by
    intro q4 q5 q6
    exact ((cg (fun t => (q4 ◇ (q4 ◇ q5)) ◇ t) (apc0 q6 q4 q4 q5)).symm).trans ((h q6 (q4 ◇ (q4 ◇ q5)) q4).symm)
  have apc2 : forall (q7 q8 q9:G), (((q9 ◇ (q9 ◇ q7)) ◇ ((q9 ◇ (q9 ◇ q7)) ◇ (q8 ◇ q7))) ◇ q8) = q9:=by
    intro q7 q8 q9
    exact ((cg (fun t => ((q9 ◇ (q9 ◇ q7)) ◇ ((q9 ◇ (q9 ◇ q7)) ◇ (q8 ◇ q7))) ◇ t) (apc1 q9 q7 q8)).symm).trans (apc1 (q9 ◇ (q9 ◇ q7)) (q8 ◇ q7) q9)
  have apc3 : forall (q10 q11:G), ((q10 ◇ (q10 ◇ q11)) ◇ (q11 ◇ q11)) = (q10 ◇ q10):=by
    intro q10 q11
    exact (((cg (fun t => q10 ◇ t) (apc2 q11 q11 q10)).symm).trans ((h ((q10 ◇ (q10 ◇ q11)) ◇ (q11 ◇ q11)) q10 q11).symm)).symm
  have apc4 : forall (q12 q13:G), (((q13 ◇ (q13 ◇ q12)) ◇ (q13 ◇ q13)) ◇ q12) = q13:=by
    intro q12 q13
    exact ((cg (fun t => t ◇ q12) (cg (fun t => (q13 ◇ (q13 ◇ q12)) ◇ t) (apc3 q13 q12))).symm).trans (apc2 q12 q12 q13)
  have apc6 : forall (q14:G), ((q14 ◇ q14) ◇ q14) = q14:=by
    intro q14
    exact ((cg (fun t => t ◇ q14) (apc3 q14 q14)).symm).trans (apc4 q14 q14)
  have apc8 : forall (q15 q16 q17:G), (((q17 ◇ (q17 ◇ q16)) ◇ q15) ◇ q16) = ((q17 ◇ q17) ◇ (q15 ◇ q17)):=by
    intro q15 q16 q17
    exact ((((cg (fun t => t ◇ q16) (cg (fun t => t ◇ q15) (cg (fun t => ((q17 ◇ q17) ◇ q17) ◇ t) (cg (fun t => t ◇ q16) (cg (fun t => (q17 ◇ q17) ◇ t) (apc6 q17)))))).trans (cg (fun t => t ◇ q16) (cg (fun t => t ◇ q15) (cg (fun t => ((q17 ◇ q17) ◇ q17) ◇ t) (cg (fun t => t ◇ q16) (apc6 q17)))))).trans (cg (fun t => t ◇ q16) (cg (fun t => t ◇ q15) (cg (fun t => t ◇ (q17 ◇ q16)) (apc6 q17))))).symm).trans (((cg (fun t => t ◇ q16) (cg (fun t => t ◇ q15) (cg (fun t => t ◇ (((q17 ◇ q17) ◇ ((q17 ◇ q17) ◇ q17)) ◇ q16)) (cg (fun t => (q17 ◇ q17) ◇ t) (apc6 q17))))).symm).trans (apc0 q15 q16 (q17 ◇ q17) q17))
  have apc10 : forall (q0 q18 q2 q1:G), (q2 ◇ (((q2 ◇ q0) ◇ q18) ◇ ((q2 ◇ q2) ◇ (q0 ◇ q2)))) = q18:=by
    intro q0 q18 q2 q1
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => ((q2 ◇ q0) ◇ q18) ◇ t) (apc8 q0 q1 q2))).symm).trans (((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (((q2 ◇ (q2 ◇ q1)) ◇ q0) ◇ q1)) (cg (fun t => t ◇ q18) (cg (fun t => q2 ◇ t) ((h q0 q2 q1).symm))))).symm).trans ((h q18 q2 (((q2 ◇ (q2 ◇ q1)) ◇ q0) ◇ q1)).symm))
  have apc11 : forall (q19:G), (q19 ◇ q19) = q19:=by
    intro q19
    exact (((cg (fun t => q19 ◇ t) (apc1 (q19 ◇ q19) q19 q19)).symm).trans (apc10 q19 ((q19 ◇ q19) ◇ q19) q19 q19)).trans (apc6 q19)
  have apc15 : forall (q20 q21:G), (q21 ◇ (q21 ◇ q20)) = q21:=by
    intro q20 q21
    exact ((apc11 (q21 ◇ (q21 ◇ q20))).symm).trans (apc1 q21 q20 q21)
  have apc16 : forall (q0 q1 q2 q3:G), ((q2 ◇ q0) ◇ q1) = ((q2 ◇ q0) ◇ q0):=by
    intro q0 q1 q2 q3
    exact ((((cg (fun t => t ◇ q1) (cg (fun t => t ◇ q0) (cg (fun t => (q2 ◇ (q2 ◇ q3)) ◇ t) (cg (fun t => t ◇ q1) (apc15 q3 q2))))).trans (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q0) (cg (fun t => t ◇ (q2 ◇ q1)) (apc15 q3 q2))))).trans (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q0) (apc15 q1 q2)))).symm).trans (((apc0 q0 q1 q2 q3).trans ((apc0 q0 q0 q2 q3).symm)).trans (((cg (fun t => t ◇ q0) (cg (fun t => t ◇ q0) (cg (fun t => (q2 ◇ (q2 ◇ q3)) ◇ t) (cg (fun t => t ◇ q0) (apc15 q3 q2))))).trans (cg (fun t => t ◇ q0) (cg (fun t => t ◇ q0) (cg (fun t => t ◇ (q2 ◇ q0)) (apc15 q3 q2))))).trans (cg (fun t => t ◇ q0) (cg (fun t => t ◇ q0) (apc15 q0 q2)))))
  have apc17 : forall (q22 q23 q24:G), ((q23 ◇ q22) ◇ q22) = q24:=by
    intro q22 q23 q24
    exact ((apc16 q22 ((((q23 ◇ q22) ◇ ((q23 ◇ q22) ◇ q22)) ◇ q24) ◇ q22) q23 q22).symm).trans ((h q24 (q23 ◇ q22) q22).symm)
  exact ((apc17 x (((y ◇ ((z ◇ y) ◇ w)) ◇ u) ◇ v) x).symm).trans (apc17 x (((y ◇ ((z ◇ y) ◇ w)) ◇ u) ◇ v) (((y ◇ ((z ◇ y) ◇ w)) ◇ u) ◇ v))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_15632_to_38679 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_15632_to_38679
