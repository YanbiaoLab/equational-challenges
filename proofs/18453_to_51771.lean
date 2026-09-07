-- Equation18453 → Equation51771
-- Recorded verdict: true
-- Premise: x = (y * z) * (y * ((y * y) * x))
-- Conclusion: x * y = ((z * y) * (x * w)) * y
-- Original submission SHA-256: f36c0295b13dca752ee500ae2eced16e30a82fa83a19b358f7ddb9a7c8ac072a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ (y ◇ ((y ◇ y) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ y) ◇ (x ◇ w)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ ((q1 ◇ q1) ◇ q0)) = ((q1 ◇ q2) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => (q1 ◇ q2) ◇ t) (congrArg (fun t => q1 ◇ t) ((h q0 q1 q1).symm))).symm).trans ((h (q1 ◇ ((q1 ◇ q1) ◇ q0)) q1 q2).symm)).symm
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ q2) ◇ (q1 ◇ q0)) = ((q1 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact ((apc0 q0 q1 q2).symm).trans (apc0 q0 q1 q0)
  have apc2 : forall (q0 q1 q2:G), (q1 ◇ ((q1 ◇ q1) ◇ q0)) = ((q1 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact (apc0 q0 q1 q2).trans (apc1 q0 q1 q2)
  have apc3 : forall (q3 q4 q5 q6:G), (((q4 ◇ q5) ◇ q6) ◇ ((q4 ◇ q5) ◇ q6)) = (q3 ◇ ((q4 ◇ q5) ◇ q6)):=by
    intro q3 q4 q5 q6
    exact (((congrArg (fun t => t ◇ ((q4 ◇ q5) ◇ q6)) ((h q3 q4 q5).symm)).symm).trans (apc1 q6 (q4 ◇ q5) (q4 ◇ ((q4 ◇ q4) ◇ q3)))).symm
  have apc5 : forall (q7 q8 q9 q10 q11:G), (q8 ◇ ((q9 ◇ q10) ◇ q11)) = (q7 ◇ ((q9 ◇ q10) ◇ q11)):=by
    intro q7 q8 q9 q10 q11
    exact (((apc3 q7 q9 q10 q11).symm).trans (apc3 q8 q9 q10 q11)).symm
  have apc7 : forall (q12 q13 q14:G), (q12 ◇ ((q14 ◇ q14) ◇ q13)) = ((q14 ◇ q13) ◇ (q14 ◇ q13)):=by
    intro q12 q13 q14
    exact ((apc5 q12 q14 q14 q14 q13).symm).trans (apc2 q13 q14 q12)
  have apc8 : forall (q15 q16:G), (((q15 ◇ q16) ◇ (q15 ◇ q16)) ◇ ((q15 ◇ q16) ◇ (q15 ◇ q16))) = q16:=by
    intro q15 q16
    exact (((((congrArg (fun t => t ◇ (q15 ◇ (((q15 ◇ q15) ◇ (q15 ◇ q15)) ◇ q16))) (apc7 q15 q16 (q15 ◇ q15))).trans (congrArg (fun t => t ◇ (q15 ◇ (((q15 ◇ q15) ◇ (q15 ◇ q15)) ◇ q16))) (apc7 ((q15 ◇ q15) ◇ q16) q16 q15))).trans (congrArg (fun t => ((q15 ◇ q16) ◇ (q15 ◇ q16)) ◇ t) (apc7 q15 q16 (q15 ◇ q15)))).trans (congrArg (fun t => ((q15 ◇ q16) ◇ (q15 ◇ q16)) ◇ t) (apc7 ((q15 ◇ q15) ◇ q16) q16 q15))).symm).trans (((apc7 ((q15 ◇ q15) ◇ q15) (((q15 ◇ q15) ◇ (q15 ◇ q15)) ◇ q16) q15).symm).trans ((h q16 (q15 ◇ q15) q15).symm))
  have apc9 : forall (q17 q18 q19 q20:G), (q19 ◇ q17) = (q18 ◇ q17):=by
    intro q17 q18 q19 q20
    exact (((congrArg (fun t => q19 ◇ t) (apc8 q20 q17)).symm).trans (apc5 q18 q19 (q20 ◇ q17) (q20 ◇ q17) ((q20 ◇ q17) ◇ (q20 ◇ q17)))).trans (congrArg (fun t => q18 ◇ t) (apc8 q20 q17))
  exact (apc9 y (x ◇ y) x (x ◇ y)).trans ((apc9 y (x ◇ y) ((z ◇ y) ◇ (x ◇ w)) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_18453_to_51771 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_18453_to_51771
