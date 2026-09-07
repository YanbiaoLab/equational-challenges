-- Equation6879 → Equation151
-- Recorded verdict: true
-- Premise: x = y ◇ (y ◇ ((z ◇ x) ◇ (x ◇ z)))
-- Conclusion: x = (x ◇ x) ◇ (x ◇ x)
-- Original submission SHA-256: f965541af206d8eddfd742665d4595cc0b9a8e02287ca7f59ae25297276f1e96
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ ((z ◇ x) ◇ (x ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = (x ◇ x) ◇ (x ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), (((q0 ◇ q1) ◇ (q1 ◇ q0)) ◇ q0) = (q1 ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => ((q0 ◇ q1) ◇ (q1 ◇ q0)) ◇ t) ((h q0 ((q0 ◇ q1) ◇ (q1 ◇ q0)) q1).symm)).symm).trans ((h (q1 ◇ q0) ((q0 ◇ q1) ◇ (q1 ◇ q0)) (q0 ◇ q1)).symm)
  have apc1 : forall (x y z:G), (y ◇ (y ◇ ((z ◇ x) ◇ (x ◇ z)))) = (x ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc2 : forall (q2:G), (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2)))) = q2:=by
    intro q2
    exact ((apc1 q2 q2 q2).symm).trans ((h q2 q2 q2).symm)
  have apc4 : forall (q0 q1 q3 q4:G), (q3 ◇ (q3 ◇ (q0 ◇ ((q4 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ q4)))) = (q4 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))):=by
    intro q0 q1 q3 q4
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q3 ◇ t) (cg (fun t => t ◇ ((q4 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ q4)) ((h q0 q4 q1).symm)))).symm).trans ((h (q4 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) q3 q4).symm)
  have apc6 : forall (q5 q6 q7:G), (((((q7 ◇ q6) ◇ (q6 ◇ q7)) ◇ q5) ◇ (q5 ◇ ((q7 ◇ q6) ◇ (q6 ◇ q7)))) ◇ (q5 ◇ ((q7 ◇ q6) ◇ (q6 ◇ q7)))) = q6:=by
    intro q5 q6 q7
    exact ((cg (fun t => ((((q7 ◇ q6) ◇ (q6 ◇ q7)) ◇ q5) ◇ (q5 ◇ ((q7 ◇ q6) ◇ (q6 ◇ q7)))) ◇ t) (apc0 ((q7 ◇ q6) ◇ (q6 ◇ q7)) q5)).symm).trans ((h q6 ((((q7 ◇ q6) ◇ (q6 ◇ q7)) ◇ q5) ◇ (q5 ◇ ((q7 ◇ q6) ◇ (q6 ◇ q7)))) q7).symm)
  have apc7 : forall (q8 q9:G), ((((q8 ◇ q8) ◇ (q8 ◇ q8)) ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))) ◇ (((q8 ◇ q8) ◇ (q8 ◇ q8)) ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8)))) = (q9 ◇ (q9 ◇ ((q8 ◇ q8) ◇ q8))):=by
    intro q8 q9
    exact (((cg (fun t => q9 ◇ t) (cg (fun t => q9 ◇ t) (cg (fun t => (q8 ◇ q8) ◇ t) (apc6 ((q8 ◇ q8) ◇ (q8 ◇ q8)) q8 q8)))).symm).trans (apc4 (q8 ◇ q8) (q8 ◇ q8) q9 (((q8 ◇ q8) ◇ (q8 ◇ q8)) ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))))).symm
  have apc9 : forall (q8 q9:G), (q9 ◇ (q9 ◇ ((q8 ◇ q8) ◇ q8))) = (q8 ◇ (q8 ◇ ((q8 ◇ q8) ◇ q8))):=by
    intro q8 q9
    exact ((apc7 q8 q9).symm).trans (apc7 q8 q8)
  have apc10 : forall (q0 q1 q10 q3:G), (q3 ◇ (q3 ◇ (((q10 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ q10) ◇ q0))) = q10:=by
    intro q0 q1 q10 q3
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q3 ◇ t) (cg (fun t => ((q10 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ q10) ◇ t) ((h q0 q10 q1).symm)))).symm).trans ((h q10 q3 (q10 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))).symm)
  have apc11 : forall (q11 q12:G), (((q11 ◇ q11) ◇ (q11 ◇ q11)) ◇ ((q11 ◇ q11) ◇ (q11 ◇ q11))) = (q12 ◇ (q12 ◇ (q11 ◇ (q11 ◇ q11)))):=by
    intro q11 q12
    exact (((cg (fun t => q12 ◇ t) (cg (fun t => q12 ◇ t) (cg (fun t => t ◇ (q11 ◇ q11)) (apc6 ((q11 ◇ q11) ◇ (q11 ◇ q11)) q11 q11)))).symm).trans (apc10 (q11 ◇ q11) (q11 ◇ q11) (((q11 ◇ q11) ◇ (q11 ◇ q11)) ◇ ((q11 ◇ q11) ◇ (q11 ◇ q11))) q12)).symm
  have apc12 : forall (q13:G), ((((q13 ◇ q13) ◇ (q13 ◇ q13)) ◇ ((q13 ◇ q13) ◇ (q13 ◇ q13))) ◇ (((q13 ◇ q13) ◇ (q13 ◇ q13)) ◇ ((q13 ◇ q13) ◇ (q13 ◇ q13)))) = ((q13 ◇ q13) ◇ q13):=by
    intro q13
    exact (((cg (fun t => (q13 ◇ q13) ◇ t) ((h q13 (q13 ◇ q13) q13).symm)).symm).trans ((apc11 (q13 ◇ q13) (q13 ◇ q13)).symm)).symm
  have apc14 : forall (q14 q15:G), (q14 ◇ (q14 ◇ ((q14 ◇ q14) ◇ q14))) = ((q14 ◇ q14) ◇ (q14 ◇ q14)):=by
    intro q14 q15
    exact ((apc9 q14 q15).symm).trans (((cg (fun t => q15 ◇ t) (cg (fun t => q15 ◇ t) (apc12 q14))).symm).trans ((h ((q14 ◇ q14) ◇ (q14 ◇ q14)) q15 ((q14 ◇ q14) ◇ (q14 ◇ q14))).symm))
  have apc15 : forall (q8 q9:G), (q9 ◇ (q9 ◇ ((q8 ◇ q8) ◇ q8))) = ((q8 ◇ q8) ◇ (q8 ◇ q8)):=by
    intro q8 q9
    exact (apc9 q8 q9).trans (apc14 q8 (q8 ◇ (q8 ◇ ((q8 ◇ q8) ◇ q8))))
  have apc17 : forall (q16:G), ((q16 ◇ (q16 ◇ q16)) ◇ ((q16 ◇ q16) ◇ (q16 ◇ q16))) = (q16 ◇ q16):=by
    intro q16
    exact ((cg (fun t => (q16 ◇ (q16 ◇ q16)) ◇ t) (apc15 q16 (q16 ◇ (q16 ◇ q16)))).symm).trans ((h (q16 ◇ q16) (q16 ◇ (q16 ◇ q16)) q16).symm)
  have apc18 : forall (q17:G), ((q17 ◇ (q17 ◇ q17)) ◇ (q17 ◇ q17)) = q17:=by
    intro q17
    exact ((cg (fun t => (q17 ◇ (q17 ◇ q17)) ◇ t) (apc17 q17)).symm).trans ((h q17 (q17 ◇ (q17 ◇ q17)) q17).symm)
  have apc19 : forall (q18:G), (((q18 ◇ q18) ◇ ((q18 ◇ q18) ◇ (q18 ◇ q18))) ◇ (q18 ◇ q18)) = q18:=by
    intro q18
    exact ((cg (fun t => ((q18 ◇ q18) ◇ ((q18 ◇ q18) ◇ (q18 ◇ q18))) ◇ t) (apc18 (q18 ◇ q18))).symm).trans ((h q18 ((q18 ◇ q18) ◇ ((q18 ◇ q18) ◇ (q18 ◇ q18))) q18).symm)
  have apc20 : forall (q19 q20:G), (q20 ◇ (q20 ◇ (q19 ◇ q19))) = (q19 ◇ q19):=by
    intro q19 q20
    exact ((cg (fun t => q20 ◇ t) (cg (fun t => q20 ◇ t) (cg (fun t => t ◇ q19) (apc19 q19)))).symm).trans (apc10 q19 q19 (q19 ◇ q19) q20)
  have apc21 : forall (q2:G), ((q2 ◇ q2) ◇ (q2 ◇ q2)) = q2:=by
    intro q2
    exact ((apc20 (q2 ◇ q2) q2).symm).trans (apc2 q2)
  exact (apc21 x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6879_to_151 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6879_to_151
