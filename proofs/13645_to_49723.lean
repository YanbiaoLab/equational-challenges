-- Equation13645 → Equation49723
-- Recorded verdict: true
-- Premise: x = x * ((y * ((z * w) * x)) * w)
-- Conclusion: x * y = (x * (z * (y * y))) * w
-- Original submission SHA-256: 5229c6636922dfb7f1bf3cd6525da5c31c91df879d13b62eba0833962447638f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ ((y ◇ ((z ◇ w) ◇ x)) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (x ◇ (z ◇ (y ◇ y))) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ (q2 ◇ ((q0 ◇ q1) ◇ q2))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ q2)) ((h q2 q0 q0 q1).symm))).symm).trans ((h q1 q2 q0 ((q0 ◇ q1) ◇ q2)).symm)
  have apc1 : forall (q3 q4:G), (((q3 ◇ q4) ◇ q4) ◇ q4) = ((q3 ◇ q4) ◇ q4):=by
    intro q3 q4
    exact ((cg (fun t => ((q3 ◇ q4) ◇ q4) ◇ t) ((h q4 q3 q3 q4).symm)).symm).trans (apc0 q3 ((q3 ◇ q4) ◇ q4) q4)
  have apc2 : forall (q5 q6 q7:G), (q6 ◇ ((q7 ◇ ((q5 ◇ q6) ◇ q6)) ◇ q6)) = q6:=by
    intro q5 q6 q7
    exact ((cg (fun t => q6 ◇ t) (cg (fun t => t ◇ q6) (cg (fun t => q7 ◇ t) (apc1 q5 q6)))).symm).trans ((h q6 q7 (q5 ◇ q6) q6).symm)
  have apc3 : forall (q8 q9 q10 q11:G), (((q8 ◇ q10) ◇ (q11 ◇ q9)) ◇ (q10 ◇ q9)) = ((q8 ◇ q10) ◇ (q11 ◇ q9)):=by
    intro q8 q9 q10 q11
    exact ((cg (fun t => ((q8 ◇ q10) ◇ (q11 ◇ q9)) ◇ t) (cg (fun t => t ◇ q9) (apc0 q8 q10 (q11 ◇ q9)))).symm).trans ((h ((q8 ◇ q10) ◇ (q11 ◇ q9)) q10 q11 q9).symm)
  have apc4 : forall (q12 q13 q14 q15:G), ((q12 ◇ q13) ◇ (q13 ◇ (q12 ◇ q13))) = (q12 ◇ q13):=by
    intro q12 q13 q14 q15
    exact (((cg (fun t => t ◇ (q13 ◇ (q12 ◇ q13))) (apc2 q14 (q12 ◇ q13) q15)).symm).trans (apc3 q12 (q12 ◇ q13) q13 (q15 ◇ ((q14 ◇ (q12 ◇ q13)) ◇ (q12 ◇ q13))))).trans (apc2 q14 (q12 ◇ q13) q15)
  have apc5 : forall (q16 q17:G), ((q17 ◇ (q16 ◇ q17)) ◇ (q16 ◇ q17)) = (q17 ◇ (q16 ◇ q17)):=by
    intro q16 q17
    exact ((cg (fun t => (q17 ◇ (q16 ◇ q17)) ◇ t) (apc4 q16 q17 q16 q16)).symm).trans (apc4 q17 (q16 ◇ q17) q16 q16)
  have apc6 : forall (q18 q19:G), ((q18 ◇ q19) ◇ (q18 ◇ q19)) = (q18 ◇ q19):=by
    intro q18 q19
    exact ((cg (fun t => (q18 ◇ q19) ◇ t) (apc4 q18 q19 ((q18 ◇ q19) ◇ (q19 ◇ (q18 ◇ q19))) ((q18 ◇ q19) ◇ (q19 ◇ (q18 ◇ q19))))).symm).trans (((cg (fun t => (q18 ◇ q19) ◇ t) (cg (fun t => (q18 ◇ q19) ◇ t) (apc5 q18 q19))).symm).trans (apc0 q19 (q18 ◇ q19) (q18 ◇ q19)))
  have apc7 : forall (q20 q21 q22:G), (q20 ◇ q20) = q20:=by
    intro q20 q21 q22
    exact ((cg (fun t => q20 ◇ t) (apc0 q21 q20 q22)).symm).trans ((((cg (fun t => t ◇ (q20 ◇ (q22 ◇ ((q21 ◇ q20) ◇ q22)))) (apc0 q21 q20 q22)).symm).trans (apc6 q20 (q22 ◇ ((q21 ◇ q20) ◇ q22)))).trans (apc0 q21 q20 q22))
  have apc13 : forall (q23 q24:G), (q24 ◇ (q23 ◇ q24)) = q24:=by
    intro q23 q24
    exact ((cg (fun t => q24 ◇ t) (apc7 (q23 ◇ q24) ((q23 ◇ q24) ◇ (q23 ◇ q24)) ((q23 ◇ q24) ◇ (q23 ◇ q24)))).symm).trans (((cg (fun t => q24 ◇ t) (cg (fun t => (q23 ◇ q24) ◇ t) (apc6 q23 q24))).symm).trans (apc0 q23 q24 (q23 ◇ q24)))
  have apc15 : forall (q0 q1 q2 q23 q24:G), (q1 ◇ q2) = q1:=by
    intro q0 q1 q2 q23 q24
    exact ((cg (fun t => q1 ◇ t) (apc13 (q0 ◇ q1) q2)).symm).trans (apc0 q0 q1 q2)
  exact (calc
    (x ◇ y) = x:=apc15 (x ◇ y) x y (x ◇ y) (x ◇ y)
    _ = ((x ◇ (z ◇ (y ◇ y))) ◇ w):=((((cg (fun t => t ◇ w) (cg (fun t => x ◇ t) (cg (fun t => z ◇ t) (apc15 (y ◇ y) y y (y ◇ y) (y ◇ y))))).trans (cg (fun t => t ◇ w) (cg (fun t => x ◇ t) (apc15 (z ◇ y) z y (z ◇ y) (z ◇ y))))).trans (cg (fun t => t ◇ w) (apc15 (x ◇ z) x z (x ◇ z) (x ◇ z)))).trans (apc15 (x ◇ w) x w (x ◇ w) (x ◇ w))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_13645_to_49723 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_13645_to_49723
