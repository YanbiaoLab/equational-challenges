-- Equation22443 → Equation18017
-- Recorded verdict: true
-- Premise: x = (y ◇ (x ◇ x)) ◇ ((x ◇ y) ◇ z)
-- Conclusion: x = (x ◇ y) ◇ (z ◇ ((z ◇ y) ◇ w))
-- Original submission SHA-256: 7e0c6bb6499a7b15ddcf5d5725a7028fe76db31781dfdb213440bc93c4a2f5d8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ x)) ◇ ((x ◇ y) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ y) ◇ (z ◇ ((z ◇ y) ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), (((q0 ◇ q0) ◇ (q1 ◇ q1)) ◇ q0) = q1:=by
    intro q0 q1
    exact ((cg (fun t => ((q0 ◇ q0) ◇ (q1 ◇ q1)) ◇ t) ((h q0 q1 q0).symm)).symm).trans ((h q1 (q0 ◇ q0) ((q0 ◇ q1) ◇ q0)).symm)
  have apc1 : forall (q2:G), ((q2 ◇ q2) ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2))) = q2:=by
    intro q2
    exact ((cg (fun t => t ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2))) (apc0 (q2 ◇ q2) (q2 ◇ q2))).symm).trans (apc0 ((q2 ◇ q2) ◇ (q2 ◇ q2)) q2)
  have apc2 : forall (q3:G), ((q3 ◇ (q3 ◇ q3)) ◇ q3) = q3:=by
    intro q3
    exact ((cg (fun t => (q3 ◇ (q3 ◇ q3)) ◇ t) (apc1 q3)).symm).trans ((h q3 q3 ((q3 ◇ q3) ◇ (q3 ◇ q3))).symm)
  have apc3 : forall (q4 q5:G), ((q4 ◇ q4) ◇ ((q4 ◇ q4) ◇ q5)) = q4:=by
    intro q4 q5
    exact ((cg (fun t => (q4 ◇ q4) ◇ t) (cg (fun t => t ◇ q5) (cg (fun t => q4 ◇ t) (apc1 q4)))).symm).trans (((cg (fun t => t ◇ ((q4 ◇ ((q4 ◇ q4) ◇ ((q4 ◇ q4) ◇ (q4 ◇ q4)))) ◇ q5)) (apc2 (q4 ◇ q4))).symm).trans ((h q4 ((q4 ◇ q4) ◇ ((q4 ◇ q4) ◇ (q4 ◇ q4))) q5).symm))
  have apc4 : forall (q6:G), ((q6 ◇ q6) ◇ q6) = q6:=by
    intro q6
    exact ((cg (fun t => (q6 ◇ q6) ◇ t) (apc3 q6 q6)).symm).trans (apc3 q6 ((q6 ◇ q6) ◇ q6))
  have apc5 : forall (q7:G), ((q7 ◇ q7) ◇ (q7 ◇ q7)) = q7:=by
    intro q7
    exact ((cg (fun t => t ◇ (q7 ◇ q7)) (apc4 (q7 ◇ q7))).symm).trans (apc0 (q7 ◇ q7) q7)
  have apc6 : forall (q8 q9:G), ((q8 ◇ (q9 ◇ q9)) ◇ (q8 ◇ q8)) = q9:=by
    intro q8 q9
    exact ((cg (fun t => t ◇ (q8 ◇ q8)) (cg (fun t => t ◇ (q9 ◇ q9)) (apc5 q8))).symm).trans (apc0 (q8 ◇ q8) q9)
  have apc7 : forall (q10 q11:G), ((q11 ◇ q10) ◇ (q11 ◇ q11)) = q10:=by
    intro q10 q11
    exact (((cg (fun t => t ◇ (q11 ◇ q11)) (cg (fun t => q11 ◇ t) (apc6 (q10 ◇ q10) q10))).symm).trans (apc6 q11 ((q10 ◇ q10) ◇ (q10 ◇ q10)))).trans (apc5 q10)
  have apc10 : forall (q12:G), (q12 ◇ (q12 ◇ q12)) = q12:=by
    intro q12
    exact (((cg (fun t => q12 ◇ t) (cg (fun t => t ◇ ((q12 ◇ q12) ◇ (q12 ◇ q12))) (apc7 q12 q12))).trans (cg (fun t => q12 ◇ t) (cg (fun t => q12 ◇ t) (apc7 q12 q12)))).symm).trans ((((cg (fun t => t ◇ (((q12 ◇ q12) ◇ (q12 ◇ q12)) ◇ ((q12 ◇ q12) ◇ (q12 ◇ q12)))) (apc6 (q12 ◇ q12) q12)).symm).trans (apc5 ((q12 ◇ q12) ◇ (q12 ◇ q12)))).trans (apc7 q12 q12))
  have apc11 : forall (q13 q14:G), (q13 ◇ (q13 ◇ q14)) = q13:=by
    intro q13 q14
    exact ((cg (fun t => t ◇ (q13 ◇ q14)) (apc7 q13 q13)).symm).trans (((cg (fun t => ((q13 ◇ q13) ◇ (q13 ◇ q13)) ◇ t) (cg (fun t => t ◇ q14) (apc10 q13))).symm).trans ((h q13 (q13 ◇ q13) q14).symm))
  have apc12 : forall (q15 q16 q17:G), (q15 ◇ (q16 ◇ q17)) = q16:=by
    intro q15 q16 q17
    exact ((cg (fun t => t ◇ (q16 ◇ q17)) (apc7 q15 q16)).symm).trans (((cg (fun t => ((q16 ◇ q15) ◇ (q16 ◇ q16)) ◇ t) (cg (fun t => t ◇ q17) (apc11 q16 q15))).symm).trans ((h q16 (q16 ◇ q15) q17).symm))
  have apc13 : forall (q12:G), (q12 ◇ q12) = q12:=by
    intro q12
    exact (((apc6 (q12 ◇ q12) q12).symm).trans (apc5 (q12 ◇ q12))).symm
  have apc15 : forall (q0 q18 q19 q20:G), (q18 ◇ q0) = q0:=by
    intro q0 q18 q19 q20
    exact ((((((cg (fun t => t ◇ (q0 ◇ q19)) (cg (fun t => ((q0 ◇ q18) ◇ q20) ◇ t) (cg (fun t => t ◇ (q18 ◇ (q0 ◇ q0))) (cg (fun t => q18 ◇ t) (apc13 q0))))).trans (cg (fun t => t ◇ (q0 ◇ q19)) (cg (fun t => ((q0 ◇ q18) ◇ q20) ◇ t) (cg (fun t => (q18 ◇ q0) ◇ t) (cg (fun t => q18 ◇ t) (apc13 q0)))))).trans (cg (fun t => t ◇ (q0 ◇ q19)) (cg (fun t => ((q0 ◇ q18) ◇ q20) ◇ t) (apc12 (q18 ◇ q0) q18 q0)))).trans (apc12 (((q0 ◇ q18) ◇ q20) ◇ q18) q0 q19)).symm).trans ((((cg (fun t => (((q0 ◇ q18) ◇ q20) ◇ ((q18 ◇ (q0 ◇ q0)) ◇ (q18 ◇ (q0 ◇ q0)))) ◇ t) (cg (fun t => t ◇ q19) ((h q0 q18 q20).symm))).symm).trans ((h (q18 ◇ (q0 ◇ q0)) ((q0 ◇ q18) ◇ q20) q19).symm)).trans (cg (fun t => q18 ◇ t) (apc13 q0)))).symm
  have apc16 : forall (q21 q22 q23:G), q22 = q21:=by
    intro q21 q22 q23
    exact ((((((((cg (fun t => (q23 ◇ q21) ◇ t) (cg (fun t => t ◇ q22) (cg (fun t => t ◇ q23) (cg (fun t => t ◇ (q21 ◇ q21)) (apc15 q21 q21 (q21 ◇ q21) (q21 ◇ q21)))))).trans (cg (fun t => (q23 ◇ q21) ◇ t) (cg (fun t => t ◇ q22) (cg (fun t => t ◇ q23) (cg (fun t => q21 ◇ t) (apc15 q21 q21 (q21 ◇ q21) (q21 ◇ q21))))))).trans (cg (fun t => (q23 ◇ q21) ◇ t) (cg (fun t => t ◇ q22) (cg (fun t => t ◇ q23) (apc15 q21 q21 (q21 ◇ q21) (q21 ◇ q21)))))).trans (cg (fun t => (q23 ◇ q21) ◇ t) (cg (fun t => t ◇ q22) (apc15 q23 q21 (q21 ◇ q23) (q21 ◇ q23))))).trans (cg (fun t => t ◇ (q23 ◇ q22)) (apc15 q21 q23 (q23 ◇ q21) (q23 ◇ q21)))).trans (cg (fun t => q21 ◇ t) (apc15 q22 q23 (q23 ◇ q22) (q23 ◇ q22)))).trans (apc15 q22 q21 (q21 ◇ q22) (q21 ◇ q22))).symm).trans ((((cg (fun t => t ◇ ((((q21 ◇ q21) ◇ (q21 ◇ q21)) ◇ q23) ◇ q22)) (cg (fun t => q23 ◇ t) (apc6 (q21 ◇ q21) q21))).symm).trans ((h ((q21 ◇ q21) ◇ (q21 ◇ q21)) q23 q22).symm)).trans (((cg (fun t => t ◇ (q21 ◇ q21)) (apc15 q21 q21 (q21 ◇ q21) (q21 ◇ q21))).trans (cg (fun t => q21 ◇ t) (apc15 q21 q21 (q21 ◇ q21) (q21 ◇ q21)))).trans (apc15 q21 q21 (q21 ◇ q21) (q21 ◇ q21))))
  exact (apc16 x x x).trans ((apc16 x ((x ◇ y) ◇ (z ◇ ((z ◇ y) ◇ w))) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22443_to_18017 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22443_to_18017
