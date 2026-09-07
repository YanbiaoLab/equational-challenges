-- Equation47454 → Equation52374
-- Recorded verdict: true
-- Premise: x * y = (z * z) * ((x * y) * x)
-- Conclusion: x * y = ((x * (z * z)) * z) * z
-- Original submission SHA-256: c57046fb12a8779224ffce589f567282dab7601bb7f148c266e30d2099ee594e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ z) ◇ ((x ◇ y) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((x ◇ (z ◇ z)) ◇ z) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (((q0 ◇ q1) ◇ q0) ◇ ((q0 ◇ q1) ◇ q0)) = ((q2 ◇ q2) ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => (q2 ◇ q2) ◇ t) ((h q0 q1 ((q0 ◇ q1) ◇ q0)).symm)).symm).trans ((h ((q0 ◇ q1) ◇ q0) ((q0 ◇ q1) ◇ q0) q2).symm)).symm
  have apc1 : forall (q3 q4 q5 q6 q7:G), (((q5 ◇ q5) ◇ (q3 ◇ q4)) ◇ ((q6 ◇ q7) ◇ q6)) = (q6 ◇ q7):=by
    intro q3 q4 q5 q6 q7
    exact ((congrArg (fun t => t ◇ ((q6 ◇ q7) ◇ q6)) (apc0 q3 q4 q5)).symm).trans ((h q6 q7 ((q3 ◇ q4) ◇ q3)).symm)
  have apc2 : forall (q8 q9 q10 q11:G), ((q9 ◇ q8) ◇ ((q10 ◇ q11) ◇ q10)) = (q10 ◇ q11):=by
    intro q8 q9 q10 q11
    exact ((congrArg (fun t => t ◇ ((q10 ◇ q11) ◇ q10)) ((h q9 q8 q8).symm)).symm).trans (apc1 (q9 ◇ q8) q9 q8 q10 q11)
  have apc3 : forall (q12 q13 q14 q15:G), ((q15 ◇ q14) ◇ (q12 ◇ q13)) = (q12 ◇ q13):=by
    intro q12 q13 q14 q15
    exact (((congrArg (fun t => (q15 ◇ q14) ◇ t) ((h q12 q13 ((q12 ◇ q13) ◇ q12)).symm)).symm).trans (apc2 q14 q15 ((q12 ◇ q13) ◇ q12) ((q12 ◇ q13) ◇ q12))).trans (apc2 q12 (q12 ◇ q13) q12 q13)
  have apc5 : forall (q16 q17 q18 q19:G), ((q16 ◇ q17) ◇ q18) = (q16 ◇ q17):=by
    intro q16 q17 q18 q19
    exact (((apc3 q16 q17 q19 q19).symm).trans (((congrArg (fun t => (q19 ◇ q19) ◇ t) (apc3 q16 q17 q18 (q16 ◇ q17))).symm).trans ((h (q16 ◇ q17) q18 q19).symm))).symm
  have apc6 : forall (q20 q21 q19 q16 q17:G), (q19 ◇ q19) = (q21 ◇ q20):=by
    intro q20 q21 q19 q16 q17
    exact (((congrArg (fun t => (q19 ◇ q19) ◇ t) (apc5 q16 q17 (q21 ◇ q20) ((q16 ◇ q17) ◇ (q21 ◇ q20)))).trans (apc5 q19 q19 (q16 ◇ q17) ((q19 ◇ q19) ◇ (q16 ◇ q17)))).symm).trans ((((congrArg (fun t => (q19 ◇ q19) ◇ t) (congrArg (fun t => t ◇ (q21 ◇ q20)) (apc3 q16 q17 q20 q21))).symm).trans ((h (q21 ◇ q20) (q16 ◇ q17) q19).symm)).trans (apc5 q21 q20 (q16 ◇ q17) ((q21 ◇ q20) ◇ (q16 ◇ q17))))
  exact ((apc6 y x (x ◇ y) (x ◇ y) (x ◇ y)).symm).trans (apc6 z ((x ◇ (z ◇ z)) ◇ z) (x ◇ y) (x ◇ y) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47454_to_52374 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47454_to_52374
