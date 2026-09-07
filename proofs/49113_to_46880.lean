-- Equation49113 → Equation46880
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * w) * (z * z)
-- Conclusion: x * x = (y * y) * ((x * x) * x)
-- Original submission SHA-256: 75739c5ce2e3ef40f5b5f1cd9c792b318c61e5b64cf495b33b404cc949e0b274
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ x) ◇ w) ◇ (z ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = (y ◇ y) ◇ ((x ◇ x) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc3 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc5 : forall (x y z w:G), (((z ◇ x) ◇ w) ◇ (z ◇ z)) = (((x ◇ x) ◇ x) ◇ (x ◇ x)):=by
    intro x y z w
    exact ((h x y z w).symm).trans (h x y x x)
  have apc7 : forall (q0 q1 q2 q3:G), (((q2 ◇ q1) ◇ q0) ◇ ((q2 ◇ q1) ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1 q2 q3
    exact (((apc3 ((q2 ◇ q1) ◇ q0) (q2 ◇ q2) q0 q0).symm).trans ((h q1 q3 q2 q0).symm)).trans (apc3 q1 q3 (q1 ◇ q3) (q1 ◇ q3))
  have apc8 : forall (q4 q5 q6:G), (((q6 ◇ q6) ◇ q4) ◇ ((q6 ◇ q5) ◇ q4)) = (q5 ◇ q5):=by
    intro q4 q5 q6
    exact ((congrArg (fun t => t ◇ ((q6 ◇ q5) ◇ q4)) (congrArg (fun t => t ◇ q4) (apc3 q6 q5 q4 q4))).symm).trans (apc7 q4 q5 q6 q4)
  have apc9 : forall (q7 q8 q9 q10:G), (((q8 ◇ q8) ◇ q9) ◇ ((q7 ◇ q7) ◇ q9)) = (q7 ◇ q7):=by
    intro q7 q8 q9 q10
    exact ((congrArg (fun t => t ◇ ((q7 ◇ q7) ◇ q9)) (congrArg (fun t => t ◇ q9) (apc7 q10 q8 q8 (((q8 ◇ q8) ◇ q10) ◇ ((q8 ◇ q8) ◇ q10))))).symm).trans ((((congrArg (fun t => ((((q8 ◇ q8) ◇ q10) ◇ ((q8 ◇ q8) ◇ q10)) ◇ q9) ◇ t) (congrArg (fun t => t ◇ q9) (apc8 q10 q7 q8))).symm).trans (apc8 q9 ((q8 ◇ q7) ◇ q10) ((q8 ◇ q8) ◇ q10))).trans (apc7 q10 q7 q8 (((q8 ◇ q7) ◇ q10) ◇ ((q8 ◇ q7) ◇ q10))))
  have apc10 : forall (q11 q12 q13:G), ((q12 ◇ q11) ◇ (q12 ◇ q11)) = (q13 ◇ q13):=by
    intro q11 q12 q13
    exact ((((apc3 ((q13 ◇ q13) ◇ (q12 ◇ q12)) (((q11 ◇ q11) ◇ q11) ◇ (q11 ◇ q11)) (((q13 ◇ q13) ◇ (q12 ◇ q12)) ◇ (((q11 ◇ q11) ◇ q11) ◇ (q11 ◇ q11))) (((q13 ◇ q13) ◇ (q12 ◇ q12)) ◇ (((q11 ◇ q11) ◇ q11) ◇ (q11 ◇ q11)))).trans (apc7 (q12 ◇ q12) q13 q13 (((q13 ◇ q13) ◇ (q12 ◇ q12)) ◇ ((q13 ◇ q13) ◇ (q12 ◇ q12))))).symm).trans (((congrArg (fun t => ((q13 ◇ q13) ◇ (q12 ◇ q12)) ◇ t) (apc5 q11 q11 q12 (q12 ◇ q11))).symm).trans (apc9 (q12 ◇ q11) q13 (q12 ◇ q12) q11))).symm
  have apc12 : forall (q14 q15:G), ((q14 ◇ q14) ◇ q15) = (q14 ◇ q14):=by
    intro q14 q15
    exact (((apc9 q14 (q14 ◇ q14) (q14 ◇ q14) q14).symm).trans ((h (q14 ◇ q14) q15 (q14 ◇ q14) (q14 ◇ q14)).symm)).symm
  have apc13 : forall (q16 q17:G), ((q17 ◇ q16) ◇ (q17 ◇ q16)) = (q16 ◇ q16):=by
    intro q16 q17
    exact ((apc12 (q17 ◇ q16) ((q17 ◇ q16) ◇ (q17 ◇ q16))).symm).trans (apc7 (q17 ◇ q16) q16 q17 q16)
  have apc15 : forall (q18 q19 q20 q21 q22:G), ((q19 ◇ q18) ◇ q21) = (q20 ◇ q20):=by
    intro q18 q19 q20 q21 q22
    exact (((((congrArg (fun t => t ◇ ((q19 ◇ q18) ◇ (q19 ◇ q18))) (apc12 q20 q22)).trans (congrArg (fun t => (q20 ◇ q20) ◇ t) (apc13 q18 q19))).trans (apc12 q20 (q18 ◇ q18))).symm).trans (((congrArg (fun t => t ◇ ((q19 ◇ q18) ◇ (q19 ◇ q18))) (congrArg (fun t => t ◇ q22) (apc10 q18 q19 q20))).symm).trans ((h (q19 ◇ q18) q21 (q19 ◇ q18) q22).symm))).symm
  exact ((apc15 x x x (x ◇ x) (x ◇ x)).symm).trans ((apc15 y y (x ◇ x) ((x ◇ x) ◇ x) (x ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49113_to_46880 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49113_to_46880
