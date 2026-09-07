-- Equation52594 → Equation53719
-- Recorded verdict: true
-- Premise: x * y = ((z * (x * z)) * x) * z
-- Conclusion: x * y = (((z * w) * z) * x) * y
-- Original submission SHA-256: 01237d7367ef343692a30d3839e9dd49fc00a4000728a8f90a2a123915c0d713
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ (x ◇ z)) ◇ x) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (((z ◇ w) ◇ z) ◇ x) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc1 : forall (q0 q1 q2:G), (((q1 ◇ q1) ◇ q0) ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q0) (apc0 q1 (q0 ◇ q1) q0))).symm).trans ((h q0 q2 q1).symm)).trans (apc0 q0 q2 (q0 ◇ q2))
  have apc2 : forall (q3 q4 q5:G), (((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ q5) = (q4 ◇ q4):=by
    intro q3 q4 q5
    exact ((((congrArg (fun t => t ◇ q5) (congrArg (fun t => t ◇ q3) (congrArg (fun t => t ◇ (q5 ◇ q5)) (apc0 q3 ((q5 ◇ q5) ◇ q3) (q3 ◇ ((q5 ◇ q5) ◇ q3)))))).trans (congrArg (fun t => t ◇ q5) (congrArg (fun t => t ◇ q3) (apc0 (q3 ◇ q3) (q5 ◇ q5) ((q3 ◇ q3) ◇ (q5 ◇ q5)))))).trans (congrArg (fun t => t ◇ q5) (apc1 (q3 ◇ q3) q3 (((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ q3)))).symm).trans (((congrArg (fun t => t ◇ q5) (h (q5 ◇ q5) q4 q3)).symm).trans (apc1 q4 q5 q3))
  have apc3 : forall (q6 q7 q8 q9:G), ((((q6 ◇ q6) ◇ (q6 ◇ q6)) ◇ q7) ◇ q9) = (q8 ◇ q8):=by
    intro q6 q7 q8 q9
    exact ((congrArg (fun t => t ◇ q9) ((apc2 q6 (q6 ◇ q6) q7).symm)).symm).trans (apc2 q6 q8 q9)
  have apc4 : forall (q10 q11 q12 q13:G), (((q10 ◇ q10) ◇ q11) ◇ q13) = (q12 ◇ q12):=by
    intro q10 q11 q12 q13
    exact ((congrArg (fun t => t ◇ q13) (congrArg (fun t => t ◇ q11) (apc3 q10 ((q10 ◇ q10) ◇ (q10 ◇ q10)) q10 (((q10 ◇ q10) ◇ (q10 ◇ q10)) ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10)))))).symm).trans (apc3 ((q10 ◇ q10) ◇ (q10 ◇ q10)) q11 q12 q13)
  have apc5 : forall (q14 q15 q16 q17 q18:G), ((((q14 ◇ q14) ◇ q15) ◇ q16) ◇ q18) = (q17 ◇ q17):=by
    intro q14 q15 q16 q17 q18
    exact ((congrArg (fun t => t ◇ q18) ((apc4 q14 q15 (q14 ◇ q14) q16).symm)).symm).trans (apc4 q14 (q14 ◇ q14) q17 q18)
  have apc10 : forall (q19 q20 q21:G), (q21 ◇ q21) = (q20 ◇ q19):=by
    intro q19 q20 q21
    exact ((h q20 q19 (q19 ◇ q19)).trans (apc5 q19 (q20 ◇ (q19 ◇ q19)) q20 q21 (q19 ◇ q19))).symm
  exact ((apc10 y x (x ◇ y)).symm).trans (apc10 y (((z ◇ w) ◇ z) ◇ x) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52594_to_53719 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52594_to_53719
