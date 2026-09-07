-- Equation26263 → Equation55903
-- Recorded verdict: true
-- Premise: x = (y ◇ ((z ◇ x) ◇ x)) ◇ (w ◇ w)
-- Conclusion: x ◇ (y ◇ x) = (z ◇ w) ◇ (z ◇ u)
-- Original submission SHA-256: af3782d6c31530bb02899005ea72e9bd0fec020d391b0a083930d1c88bed93e7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ ((z ◇ x) ◇ x)) ◇ (w ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ x) = (z ◇ w) ◇ (z ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3:G), ((q3 ◇ (q1 ◇ (q0 ◇ q0))) ◇ (q2 ◇ q2)) = (q0 ◇ q0):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ (q2 ◇ q2)) (congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ (q0 ◇ q0)) ((h q1 q0 q0 q0).symm)))).symm).trans ((h (q0 ◇ q0) q3 (q0 ◇ ((q0 ◇ q1) ◇ q1)) q2).symm)
  have apc1 : forall (q4 q5 q6 q7:G), ((q7 ◇ q4) ◇ (q6 ◇ q6)) = (q5 ◇ q5):=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => t ◇ (q6 ◇ q6)) (congrArg (fun t => q7 ◇ t) ((h q4 q4 q4 q5).symm))).symm).trans (apc0 q5 (q4 ◇ ((q4 ◇ q4) ◇ q4)) q6 q7)
  have apc4 : forall (q4 q5 q6 q7:G), ((q7 ◇ q4) ◇ (q6 ◇ q6)) = ((q5 ◇ q5) ◇ (q5 ◇ q5)):=by
    intro q4 q5 q6 q7
    exact (apc1 q4 q5 q6 q7).trans ((apc1 q5 q5 q5 q5).symm)
  have apc6 : forall (q8 q9 q10:G), ((q9 ◇ q9) ◇ (q9 ◇ q9)) = (q8 ◇ (q10 ◇ q10)):=by
    intro q8 q9 q10
    exact (((congrArg (fun t => t ◇ (q10 ◇ q10)) ((h q8 q8 q8 q8).symm)).symm).trans (apc4 (q8 ◇ q8) q9 q10 (q8 ◇ ((q8 ◇ q8) ◇ q8)))).symm
  have apc7 : forall (q11 q12 q13 q14 q15:G), ((q15 ◇ q13) ◇ (q14 ◇ q14)) = (q11 ◇ (q12 ◇ q12)):=by
    intro q11 q12 q13 q14 q15
    exact (((apc6 q11 q11 q12).symm).trans ((apc1 q13 (q11 ◇ q11) q14 q15).symm)).symm
  have apc10 : forall (q16 q17 q18 q19 q20:G), ((q20 ◇ q18) ◇ (q19 ◇ q19)) = (q17 ◇ q16):=by
    intro q16 q17 q18 q19 q20
    exact (((congrArg (fun t => q17 ◇ t) ((h q16 ((q16 ◇ q16) ◇ q16) q16 ((q16 ◇ q16) ◇ q16)).symm)).symm).trans ((apc7 q17 (((q16 ◇ q16) ◇ q16) ◇ ((q16 ◇ q16) ◇ q16)) q18 q19 q20).symm)).symm
  have apc13 : forall (q21 q22 q23 q24:G), ((q24 ◇ q24) ◇ (q24 ◇ q24)) = (q23 ◇ (q22 ◇ q21)):=by
    intro q21 q22 q23 q24
    exact (((congrArg (fun t => q23 ◇ t) (apc10 q21 q22 q21 q21 q21)).symm).trans ((apc6 q23 q24 (q21 ◇ q21)).symm)).symm
  exact ((apc13 x y x (x ◇ (y ◇ x))).symm).trans (apc13 u z (z ◇ w) (x ◇ (y ◇ x)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_26263_to_55903 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_26263_to_55903
