-- Equation32804 → Equation60509
-- Recorded verdict: true
-- Premise: x = (x * (((x * y) * z) * z)) * z
-- Conclusion: (x * y) * z = (x * w) * (y * z)
-- Original submission SHA-256: 6ec55a032728f33a0833de6689749dfb71534e87e149a1b761546b0decbbe3f1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (((x ◇ y) ◇ z) ◇ z)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = (x ◇ w) ◇ (y ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), ((q0 ◇ (q0 ◇ q1)) ◇ q1) = q0:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q1) (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ q1) ((h q0 q0 q1).symm)))).symm).trans ((h q0 (((q0 ◇ q0) ◇ q1) ◇ q1) q1).symm)
  have apc1 : forall (q2 q3:G), (((q2 ◇ (q2 ◇ q3)) ◇ q2) ◇ q3) = (q2 ◇ (q2 ◇ q3)):=by
    intro q2 q3
    exact ((cg (fun t => t ◇ q3) (cg (fun t => (q2 ◇ (q2 ◇ q3)) ◇ t) (apc0 q2 q3))).symm).trans (apc0 (q2 ◇ (q2 ◇ q3)) q3)
  have apc2 : forall (q4:G), (q4 ◇ (q4 ◇ q4)) = (q4 ◇ q4):=by
    intro q4
    exact (((cg (fun t => t ◇ q4) (apc0 q4 q4)).symm).trans (apc1 q4 q4)).symm
  have apc3 : forall (q5:G), ((q5 ◇ q5) ◇ (q5 ◇ q5)) = q5:=by
    intro q5
    exact ((cg (fun t => t ◇ (q5 ◇ q5)) (apc2 q5)).symm).trans (((cg (fun t => t ◇ (q5 ◇ q5)) (cg (fun t => q5 ◇ t) (apc2 q5))).symm).trans (apc0 q5 (q5 ◇ q5)))
  have apc4 : forall (q6:G), ((q6 ◇ q6) ◇ q6) = q6:=by
    intro q6
    exact ((cg (fun t => t ◇ q6) (apc2 q6)).symm).trans (apc0 q6 q6)
  have apc5 : forall (q7 q8:G), ((q7 ◇ (q7 ◇ q8)) ◇ (q7 ◇ q8)) = q7:=by
    intro q7 q8
    exact ((cg (fun t => t ◇ (q7 ◇ q8)) (cg (fun t => q7 ◇ t) (apc4 (q7 ◇ q8)))).symm).trans ((h q7 q8 (q7 ◇ q8)).symm)
  have apc8 : forall (q9 q10 q11:G), ((q10 ◇ (q10 ◇ q11)) ◇ ((q10 ◇ q11) ◇ q9)) = q10:=by
    intro q9 q10 q11
    exact ((cg (fun t => t ◇ ((q10 ◇ q11) ◇ q9)) (cg (fun t => q10 ◇ t) (apc5 (q10 ◇ q11) q9))).symm).trans ((h q10 q11 ((q10 ◇ q11) ◇ q9)).symm)
  have apc9 : forall (q12 q13:G), (q12 ◇ (q12 ◇ q13)) = (q12 ◇ q12):=by
    intro q12 q13
    exact (((cg (fun t => ((q12 ◇ q12) ◇ q12) ◇ t) (cg (fun t => t ◇ q13) (apc3 q12))).trans (cg (fun t => t ◇ (q12 ◇ q13)) (apc4 q12))).symm).trans (((cg (fun t => t ◇ (((q12 ◇ q12) ◇ (q12 ◇ q12)) ◇ q13)) (cg (fun t => (q12 ◇ q12) ◇ t) (apc3 q12))).symm).trans (apc8 q13 (q12 ◇ q12) (q12 ◇ q12)))
  have apc10 : forall (q14 q15 q16:G), (((q14 ◇ q14) ◇ ((q14 ◇ q15) ◇ q15)) ◇ q15) = (q14 ◇ q14):=by
    intro q14 q15 q16
    exact ((cg (fun t => t ◇ q15) (cg (fun t => t ◇ ((q14 ◇ q15) ◇ q15)) (apc9 q14 q16))).symm).trans ((((cg (fun t => t ◇ q15) (cg (fun t => (q14 ◇ (q14 ◇ q16)) ◇ t) (cg (fun t => t ◇ q15) (cg (fun t => t ◇ q15) (apc0 q14 q16))))).symm).trans ((h (q14 ◇ (q14 ◇ q16)) q16 q15).symm)).trans (apc9 q14 q16))
  have apc12 : forall (q0 q1 q12 q13:G), ((q0 ◇ q0) ◇ q1) = q0:=by
    intro q0 q1 q12 q13
    exact ((cg (fun t => t ◇ q1) (apc9 q0 q1)).symm).trans (apc0 q0 q1)
  have apc13 : forall (q17 q18:G), (q17 ◇ q18) = (q17 ◇ q17):=by
    intro q17 q18
    exact (((cg (fun t => t ◇ q18) (cg (fun t => (q17 ◇ q17) ◇ t) (apc12 q17 q18 ((q17 ◇ q17) ◇ q18) ((q17 ◇ q17) ◇ q18)))).trans (cg (fun t => t ◇ q18) (apc12 q17 q17 ((q17 ◇ q17) ◇ q17) ((q17 ◇ q17) ◇ q17)))).symm).trans (((cg (fun t => t ◇ q18) (cg (fun t => (q17 ◇ q17) ◇ t) (cg (fun t => t ◇ q18) (apc10 q17 q18 q17)))).symm).trans ((h (q17 ◇ q17) ((q17 ◇ q18) ◇ q18) q18).symm))
  exact (calc
    ((x ◇ y) ◇ z) = ((x ◇ x) ◇ z):=cg (fun t => t ◇ z) (apc13 x y)
    _ = ((x ◇ w) ◇ z):=cg (fun t => t ◇ z) ((apc13 x w).symm)
    _ = ((x ◇ w) ◇ (x ◇ w)):=((apc13 (x ◇ w) z).symm).symm
    _ = ((x ◇ w) ◇ (y ◇ z)):=(apc13 (x ◇ w) (y ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32804_to_60509 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_32804_to_60509
