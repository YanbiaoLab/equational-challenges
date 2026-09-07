-- Equation34846 → Equation57503
-- Recorded verdict: true
-- Premise: x = ((y * x) * ((z * w) * y)) * x
-- Conclusion: x * (x * y) = ((z * w) * z) * y
-- Original submission SHA-256: 77b2278cef46b0df649a9ec75408941f56f4515c001ed90fffbf89cde52d8b50
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ x) ◇ ((z ◇ w) ◇ y)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = ((z ◇ w) ◇ z) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), (((q1 ◇ q0) ◇ q1) ◇ q0) = q0:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q0) (cg (fun t => (q1 ◇ q0) ◇ t) ((h q1 q0 q0 q0).symm))).symm).trans ((h q0 q1 (q0 ◇ q1) ((q0 ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q2 q0 q1:G), (((q1 ◇ q0) ◇ (q2 ◇ q1)) ◇ q0) = q0:=by
    intro q2 q0 q1
    exact ((cg (fun t => t ◇ q0) (cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => t ◇ q1) ((h q2 q2 q2 q2).symm)))).symm).trans ((h q0 q1 ((q2 ◇ q2) ◇ ((q2 ◇ q2) ◇ q2)) q2).symm)
  have apc2 : forall (q3 q4:G), ((q4 ◇ ((q3 ◇ q4) ◇ q3)) ◇ q4) = q4:=by
    intro q3 q4
    exact ((cg (fun t => t ◇ q4) (cg (fun t => t ◇ ((q3 ◇ q4) ◇ q3)) (apc0 q4 q3))).symm).trans (apc0 q4 ((q3 ◇ q4) ◇ q3))
  have apc3 : forall (q5 q6:G), (q6 ◇ ((q5 ◇ q6) ◇ q5)) = ((q5 ◇ q6) ◇ q5):=by
    intro q5 q6
    exact ((cg (fun t => t ◇ ((q5 ◇ q6) ◇ q5)) (apc2 q5 q6)).symm).trans (apc0 ((q5 ◇ q6) ◇ q5) q6)
  have apc6 : forall (q7 q8 q9:G), ((q9 ◇ (q8 ◇ ((q7 ◇ q9) ◇ q7))) ◇ q9) = q9:=by
    intro q7 q8 q9
    exact ((cg (fun t => t ◇ q9) (cg (fun t => t ◇ (q8 ◇ ((q7 ◇ q9) ◇ q7))) (apc0 q9 q7))).symm).trans (apc1 q8 q9 ((q7 ◇ q9) ◇ q7))
  have apc9 : forall (q10 q11 q12:G), (q12 ◇ (q11 ◇ ((q10 ◇ q12) ◇ q10))) = (q11 ◇ ((q10 ◇ q12) ◇ q10)):=by
    intro q10 q11 q12
    exact ((cg (fun t => t ◇ (q11 ◇ ((q10 ◇ q12) ◇ q10))) (apc6 q10 q11 q12)).symm).trans (apc0 (q11 ◇ ((q10 ◇ q12) ◇ q10)) q12)
  have apc10 : forall (q13 q14 q15:G), (((q13 ◇ q14) ◇ q13) ◇ (q15 ◇ q14)) = (q15 ◇ q14):=by
    intro q13 q14 q15
    exact ((cg (fun t => ((q13 ◇ q14) ◇ q13) ◇ t) (cg (fun t => q15 ◇ t) (apc0 q14 q13))).symm).trans ((((cg (fun t => ((q13 ◇ q14) ◇ q13) ◇ t) (cg (fun t => q15 ◇ t) (cg (fun t => t ◇ q14) (apc3 q13 q14)))).symm).trans (apc9 q14 q15 ((q13 ◇ q14) ◇ q13))).trans ((cg (fun t => q15 ◇ t) (cg (fun t => t ◇ q14) (apc3 q13 q14))).trans (cg (fun t => q15 ◇ t) (apc0 q14 q13))))
  have apc11 : forall (q16 q17:G), ((q17 ◇ q16) ◇ q17) = q17:=by
    intro q16 q17
    exact ((cg (fun t => t ◇ q17) (apc10 q17 q16 q17)).symm).trans (apc0 q17 (q17 ◇ q16))
  have apc12 : forall (q16 q17 q5 q6:G), (q6 ◇ q5) = q5:=by
    intro q16 q17 q5 q6
    exact ((cg (fun t => q6 ◇ t) (apc11 q6 q5)).symm).trans ((apc3 q5 q6).trans (apc11 q6 q5))
  exact (calc
    (x ◇ (x ◇ y)) = y:=(cg (fun t => x ◇ t) (apc12 (x ◇ y) (x ◇ y) y x)).trans (apc12 (x ◇ y) (x ◇ y) y x)
    _ = (((z ◇ w) ◇ z) ◇ y):=(((cg (fun t => t ◇ y) (cg (fun t => t ◇ z) (apc12 (z ◇ w) (z ◇ w) w z))).trans (cg (fun t => t ◇ y) (apc12 (w ◇ z) (w ◇ z) z w))).trans (apc12 (z ◇ y) (z ◇ y) y z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_34846_to_57503 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_34846_to_57503
