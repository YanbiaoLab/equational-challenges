-- Equation9309 → Equation43815
-- Recorded verdict: true
-- Premise: x = y ◇ ((x ◇ x) ◇ (z ◇ (y ◇ z)))
-- Conclusion: x ◇ y = z ◇ ((x ◇ y) ◇ (z ◇ z))
-- Original submission SHA-256: 01b05559d3e733916797e1ccdf7ad6fc3ab2dd1231e1c4d2a6d3bd7f3b7c122a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ x) ◇ (z ◇ (y ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ ((x ◇ y) ◇ (z ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = q0:=by
    intro q0
    exact ((cg (fun t => (q0 ◇ q0) ◇ t) ((h (q0 ◇ q0) (q0 ◇ q0) (q0 ◇ q0)).symm)).symm).trans ((h q0 (q0 ◇ q0) ((q0 ◇ q0) ◇ (q0 ◇ q0))).symm)
  have apc1 : forall (q1 q2 q3:G), (q2 ◇ (q1 ◇ (q3 ◇ (q2 ◇ q3)))) = (q1 ◇ q1):=by
    intro q1 q2 q3
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q3 ◇ (q2 ◇ q3))) (apc0 q1))).symm).trans ((h (q1 ◇ q1) q2 q3).symm)
  have apc2 : forall (q4 q5:G), (q5 ◇ ((q4 ◇ q5) ◇ (q4 ◇ q5))) = (q4 ◇ q4):=by
    intro q4 q5
    exact ((cg (fun t => q5 ◇ t) (apc1 (q4 ◇ q5) q4 q5)).symm).trans (apc1 q4 q5 (q4 ◇ q5))
  have apc3 : forall (q6 q7:G), (((q6 ◇ q7) ◇ (q6 ◇ q7)) ◇ q6) = (q7 ◇ q7):=by
    intro q6 q7
    exact (((cg (fun t => ((q6 ◇ q7) ◇ (q6 ◇ q7)) ◇ t) (cg (fun t => (q6 ◇ q6) ◇ t) (apc2 q6 q7))).trans (cg (fun t => ((q6 ◇ q7) ◇ (q6 ◇ q7)) ◇ t) (apc0 q6))).symm).trans (((cg (fun t => ((q6 ◇ q7) ◇ (q6 ◇ q7)) ◇ t) (cg (fun t => t ◇ (q7 ◇ ((q6 ◇ q7) ◇ (q6 ◇ q7)))) (apc2 q6 q7))).symm).trans (apc2 q7 ((q6 ◇ q7) ◇ (q6 ◇ q7))))
  have apc4 : forall (q8 q9 q10:G), ((q10 ◇ (q9 ◇ q10)) ◇ q8) = (q9 ◇ (q8 ◇ q8)):=by
    intro q8 q9 q10
    exact ((((cg (fun t => q9 ◇ t) (apc3 (q10 ◇ (q9 ◇ q10)) q8)).symm).trans (apc1 (((q10 ◇ (q9 ◇ q10)) ◇ q8) ◇ ((q10 ◇ (q9 ◇ q10)) ◇ q8)) q9 q10)).trans (apc0 ((q10 ◇ (q9 ◇ q10)) ◇ q8))).symm
  have apc5 : forall (q11 q12 q13:G), ((q11 ◇ (q12 ◇ (q13 ◇ q12))) ◇ q11) = (q13 ◇ q13):=by
    intro q11 q12 q13
    exact (((cg (fun t => (q11 ◇ (q12 ◇ (q13 ◇ q12))) ◇ t) (cg (fun t => (q11 ◇ q11) ◇ t) (apc1 q11 q13 q12))).trans (cg (fun t => (q11 ◇ (q12 ◇ (q13 ◇ q12))) ◇ t) (apc0 q11))).symm).trans (((cg (fun t => (q11 ◇ (q12 ◇ (q13 ◇ q12))) ◇ t) (cg (fun t => t ◇ (q13 ◇ (q11 ◇ (q12 ◇ (q13 ◇ q12))))) (apc1 q11 q13 q12))).symm).trans (apc2 q13 (q11 ◇ (q12 ◇ (q13 ◇ q12)))))
  have apc6 : forall (q14 q15:G), (q15 ◇ (q14 ◇ q15)) = (q14 ◇ (q14 ◇ q14)):=by
    intro q14 q15
    exact (((cg (fun t => q14 ◇ t) (apc5 (q15 ◇ (q14 ◇ q15)) q15 q14)).symm).trans ((h (q15 ◇ (q14 ◇ q15)) q14 q15).symm)).symm
  have apc8 : forall (q8 q9 q10 q14 q15:G), ((q9 ◇ (q9 ◇ q9)) ◇ q8) = (q9 ◇ (q8 ◇ q8)):=by
    intro q8 q9 q10 q14 q15
    exact ((cg (fun t => t ◇ q8) (apc6 q9 q8)).symm).trans (apc4 q8 q9 q8)
  have apc9 : forall (q16 q17:G), ((q17 ◇ ((q16 ◇ q16) ◇ q16)) ◇ q17) = q16:=by
    intro q16 q17
    exact (((cg (fun t => t ◇ q17) (cg (fun t => q17 ◇ t) (cg (fun t => (q16 ◇ q16) ◇ t) (apc0 q16)))).symm).trans (apc5 q17 (q16 ◇ q16) (q16 ◇ q16))).trans (apc0 q16)
  have apc10 : forall (q18 q19:G), ((q19 ◇ q18) ◇ q19) = ((q18 ◇ q18) ◇ q18):=by
    intro q18 q19
    exact ((cg (fun t => t ◇ q19) (cg (fun t => q19 ◇ t) (apc9 q18 ((q18 ◇ q18) ◇ q18)))).symm).trans (apc9 ((q18 ◇ q18) ◇ q18) q19)
  have apc17 : forall (q8 q9 q10:G), ((q8 ◇ (q9 ◇ q8)) ◇ q8) = (q9 ◇ (q8 ◇ q8)):=by
    intro q8 q9 q10
    exact ((((cg (fun t => t ◇ q8) (apc6 q9 q10)).trans (apc8 q8 q9 ((q9 ◇ (q9 ◇ q9)) ◇ q8) ((q9 ◇ (q9 ◇ q9)) ◇ q8) ((q9 ◇ (q9 ◇ q9)) ◇ q8))).symm).trans ((apc4 q8 q9 q10).trans ((apc4 q8 q9 q8).symm))).symm
  have apc18 : forall (q20 q21:G), ((q21 ◇ q20) ◇ (q21 ◇ q21)) = q20:=by
    intro q20 q21
    exact (((apc9 q20 q21).symm).trans (((cg (fun t => t ◇ q21) (cg (fun t => q21 ◇ t) (apc10 q20 q21))).symm).trans (apc17 q21 (q21 ◇ q20) q20))).symm
  have apc19 : forall (q22 q23:G), ((q22 ◇ q22) ◇ (q23 ◇ q22)) = q23:=by
    intro q22 q23
    exact ((cg (fun t => t ◇ (q23 ◇ q22)) (cg (fun t => q22 ◇ t) (apc18 q22 q23))).symm).trans ((((cg (fun t => t ◇ (q23 ◇ q22)) (cg (fun t => t ◇ ((q23 ◇ q22) ◇ (q23 ◇ q23))) (apc18 q22 q23))).symm).trans (apc3 (q23 ◇ q22) (q23 ◇ q23))).trans (apc18 q23 q23))
  have apc27 : forall (q24 q25:G), (q24 ◇ (q25 ◇ (q24 ◇ q24))) = q25:=by
    intro q24 q25
    exact ((cg (fun t => t ◇ (q25 ◇ (q24 ◇ q24))) (apc18 q24 q24)).symm).trans (apc19 (q24 ◇ q24) q25)
  exact (apc27 z (x ◇ y)).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_9309_to_43815 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_9309_to_43815
