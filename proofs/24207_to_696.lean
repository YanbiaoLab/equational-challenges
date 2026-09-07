-- Equation24207 → Equation696
-- Recorded verdict: true
-- Premise: x = ((y ◇ x) ◇ x) ◇ ((y ◇ y) ◇ z)
-- Conclusion: x = y ◇ (x ◇ ((z ◇ z) ◇ z))
-- Original submission SHA-256: 23cbb5d32bffcbd77f72948da1b15a4bc870fc33afd8dc485fbab70b588e6aa2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ x) ◇ ((y ◇ y) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((z ◇ z) ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1) ◇ (q0 ◇ q2)) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1) ◇ t) (cg (fun t => t ◇ q2) ((h q0 q0 q0).symm))).symm).trans ((h q1 ((q0 ◇ q0) ◇ q0) q2).symm)
  have apc1 : forall (q3 q4 q5:G), ((q4 ◇ ((q4 ◇ q4) ◇ q3)) ◇ (q4 ◇ q5)) = ((q4 ◇ q4) ◇ q3):=by
    intro q3 q4 q5
    exact ((cg (fun t => t ◇ (q4 ◇ q5)) (cg (fun t => t ◇ ((q4 ◇ q4) ◇ q3)) ((h q4 q4 q3).symm))).symm).trans (apc0 q4 ((q4 ◇ q4) ◇ q3) q5)
  have apc2 : forall (q6 q7 q5:G), ((((q6 ◇ ((q6 ◇ q6) ◇ q6)) ◇ q7) ◇ q7) ◇ (((q6 ◇ q6) ◇ q6) ◇ q5)) = q7:=by
    intro q6 q7 q5
    exact ((cg (fun t => t ◇ (((q6 ◇ q6) ◇ q6) ◇ q5)) (cg (fun t => t ◇ q7) (cg (fun t => t ◇ q7) (cg (fun t => t ◇ ((q6 ◇ q6) ◇ q6)) ((h q6 q6 q6).symm))))).symm).trans (apc0 ((q6 ◇ q6) ◇ q6) q7 q5)
  have apc3 : forall (q8 q9:G), ((((q8 ◇ ((q8 ◇ q8) ◇ q8)) ◇ q9) ◇ q9) ◇ q8) = q9:=by
    intro q8 q9
    exact ((cg (fun t => (((q8 ◇ ((q8 ◇ q8) ◇ q8)) ◇ q9) ◇ q9) ◇ t) ((h q8 q8 q8).symm)).symm).trans (apc2 q8 q9 ((q8 ◇ q8) ◇ q8))
  have apc4 : forall (q10:G), (((q10 ◇ q10) ◇ q10) ◇ q10) = ((q10 ◇ q10) ◇ q10):=by
    intro q10
    exact ((cg (fun t => t ◇ q10) ((h ((q10 ◇ q10) ◇ q10) q10 q10).symm)).symm).trans (apc3 q10 ((q10 ◇ q10) ◇ q10))
  have apc5 : forall (x y z:G), (((y ◇ x) ◇ x) ◇ ((y ◇ y) ◇ z)) = (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc6 : forall (q11 q12:G), (((q11 ◇ q11) ◇ q11) ◇ (q11 ◇ q12)) = q11:=by
    intro q11 q12
    exact ((cg (fun t => t ◇ (q11 ◇ q12)) (apc4 q11)).symm).trans (((cg (fun t => t ◇ (q11 ◇ q12)) (cg (fun t => t ◇ q11) (apc4 q11))).symm).trans (apc0 q11 q11 q12))
  have apc7 : forall (q13:G), (((q13 ◇ q13) ◇ q13) ◇ ((q13 ◇ q13) ◇ q13)) = q13:=by
    intro q13
    exact ((apc5 q13 q13 q13).symm).trans ((h q13 q13 q13).symm)
  have apc8 : forall (q14 q15:G), (q14 ◇ q15) = (q14 ◇ q14):=by
    intro q14 q15
    exact ((((cg (fun t => t ◇ q14) (cg (fun t => ((q14 ◇ q14) ◇ q14) ◇ t) (cg (fun t => t ◇ q15) (apc7 q14)))).trans (cg (fun t => t ◇ q14) (apc6 q14 q15))).symm).trans ((((cg (fun t => (((q14 ◇ q14) ◇ q14) ◇ ((((q14 ◇ q14) ◇ q14) ◇ ((q14 ◇ q14) ◇ q14)) ◇ q15)) ◇ t) (apc7 q14)).symm).trans (apc1 q15 ((q14 ◇ q14) ◇ q14) ((q14 ◇ q14) ◇ q14))).trans (cg (fun t => t ◇ q15) (apc7 q14)))).symm
  have apc9 : forall (q16:G), ((q16 ◇ q16) ◇ q16) = q16:=by
    intro q16
    exact (((apc7 q16).symm).trans (((apc8 ((q16 ◇ q16) ◇ q16) q16).symm).trans (apc4 q16))).symm
  have apc10 : forall (q10 q16:G), (q10 ◇ q10) = q10:=by
    intro q10 q16
    exact ((cg (fun t => t ◇ q10) (apc9 q10)).symm).trans ((apc4 q10).trans (apc9 q10))
  have apc13 : forall (q10 q14 q15 q16:G), (q14 ◇ q15) = q14:=by
    intro q10 q14 q15 q16
    exact (apc8 q14 q15).trans (apc10 q14 (q14 ◇ q14))
  have apc14 : forall (q17 q18:G), q18 = q17:=by
    intro q17 q18
    exact (((cg (fun t => t ◇ q17) (apc13 (q18 ◇ q17) q18 q17 (q18 ◇ q17))).trans (apc13 (q18 ◇ q17) q18 q17 (q18 ◇ q17))).symm).trans (((apc13 q17 ((q18 ◇ q17) ◇ q17) ((q18 ◇ q18) ◇ q17) q17).symm).trans ((h q17 q18 q17).symm))
  exact (apc14 x x).trans ((apc14 x (y ◇ (x ◇ ((z ◇ z) ◇ z)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_24207_to_696 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_24207_to_696
