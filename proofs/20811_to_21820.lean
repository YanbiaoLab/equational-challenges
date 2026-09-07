-- Equation20811 → Equation21820
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ (((z ◇ w) ◇ x) ◇ z)
-- Conclusion: x = (y ◇ (y ◇ z)) ◇ (z ◇ (x ◇ x))
-- Original submission SHA-256: 155434a415d80750b4826f54afe151e9bf25a1a6b8e290dd79e0deb8e91f3fed
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ x) ◇ (((z ◇ w) ◇ x) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ z)) ◇ (z ◇ (x ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), ((q3 ◇ q2) ◇ ((q0 ◇ q2) ◇ (q1 ◇ q0))) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => (q3 ◇ q2) ◇ t) (congrArg (fun t => t ◇ (q1 ◇ q0)) (congrArg (fun t => t ◇ q2) ((h q0 q1 q0 q0).symm)))).symm).trans ((h q2 q3 (q1 ◇ q0) (((q0 ◇ q0) ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q2 q3:G), ((q3 ◇ q2) ◇ q2) = q2:=by
    intro q2 q3
    exact ((congrArg (fun t => (q3 ◇ q2) ◇ t) ((h q2 ((((q2 ◇ q2) ◇ q2) ◇ q2) ◇ q2) q2 q2).symm)).symm).trans ((h q2 q3 (((q2 ◇ q2) ◇ q2) ◇ q2) q2).symm)
  have apc2 : forall (q4 q5 q6:G), ((q5 ◇ q4) ◇ (q4 ◇ q6)) = q4:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => (q5 ◇ q4) ◇ t) (congrArg (fun t => t ◇ q6) (apc1 q4 q6))).symm).trans ((h q4 q5 q6 q4).symm)
  have apc4 : forall (q7 q8:G), (q7 ◇ (q7 ◇ q8)) = q7:=by
    intro q7 q8
    exact ((congrArg (fun t => t ◇ (q7 ◇ q8)) (apc1 q7 q7)).symm).trans (apc2 q7 (q7 ◇ q7) q8)
  have apc5 : forall (q9 q10 q11:G), ((q11 ◇ q10) ◇ (q9 ◇ q10)) = q10:=by
    intro q9 q10 q11
    exact ((congrArg (fun t => (q11 ◇ q10) ◇ t) (apc4 (q9 ◇ q10) q9)).symm).trans (apc0 q9 (q9 ◇ q10) q10 q11)
  have apc6 : forall (q12 q13 q14:G), ((q14 ◇ q12) ◇ q13) = q13:=by
    intro q12 q13 q14
    exact ((apc4 ((q14 ◇ q12) ◇ q13) q14).symm).trans ((h q13 (q14 ◇ q12) q14 q12).symm)
  have apc7 : forall (q15 q16:G), (q16 ◇ (q15 ◇ q16)) = q16:=by
    intro q15 q16
    exact ((congrArg (fun t => t ◇ (q15 ◇ q16)) (apc1 q16 q15)).symm).trans (apc5 q15 q16 (q15 ◇ q16))
  have apc8 : forall (q17 q18 q19 q20:G), (q17 ◇ (q19 ◇ q18)) = q19:=by
    intro q17 q18 q19 q20
    exact ((((congrArg (fun t => (q20 ◇ (q17 ◇ (q19 ◇ q18))) ◇ t) (apc6 q18 q19 q19)).trans (apc6 (q17 ◇ (q19 ◇ q18)) q19 q20)).symm).trans (((congrArg (fun t => (q20 ◇ (q17 ◇ (q19 ◇ q18))) ◇ t) (congrArg (fun t => t ◇ q19) (apc7 q17 (q19 ◇ q18)))).symm).trans ((h (q17 ◇ (q19 ◇ q18)) q20 q19 q18).symm))).symm
  have apc9 : forall (q21 q22 q23:G), q22 = q21:=by
    intro q21 q22 q23
    exact ((((congrArg (fun t => q22 ◇ t) (apc6 q22 (q21 ◇ q23) q23)).trans (apc8 q22 q23 q21 (q22 ◇ (q21 ◇ q23)))).symm).trans (((congrArg (fun t => t ◇ ((q23 ◇ q22) ◇ (q21 ◇ q23))) (apc1 q22 q23)).symm).trans (apc0 q23 q21 q22 (q23 ◇ q22)))).symm
  exact (apc9 x x x).trans ((apc9 x ((y ◇ (y ◇ z)) ◇ (z ◇ (x ◇ x))) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_20811_to_21820 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_20811_to_21820
