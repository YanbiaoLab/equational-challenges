-- Equation29404 → Equation43583
-- Recorded verdict: true
-- Premise: x = (x ◇ (y ◇ (z ◇ (y ◇ z)))) ◇ z
-- Conclusion: x ◇ y = x ◇ ((z ◇ y) ◇ (y ◇ z))
-- Original submission SHA-256: 4e27333da2fba7ec95a81a3ae3c6812fb9f15450d23a1d87d6a1558eac0fa9f8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (y ◇ (z ◇ (y ◇ z)))) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = x ◇ ((z ◇ y) ◇ (y ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (q0 ◇ (q1 ◇ ((q2 ◇ (q3 ◇ (q2 ◇ q3))) ◇ (q1 ◇ (q2 ◇ (q3 ◇ (q2 ◇ q3))))))) = (q0 ◇ q3):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => t ◇ q3) ((h q0 q1 (q2 ◇ (q3 ◇ (q2 ◇ q3)))).symm)).symm).trans ((h (q0 ◇ (q1 ◇ ((q2 ◇ (q3 ◇ (q2 ◇ q3))) ◇ (q1 ◇ (q2 ◇ (q3 ◇ (q2 ◇ q3))))))) q2 q3).symm)).symm
  have apc1 : forall (q4 q5 q6 q7 q8:G), (q5 ◇ ((q4 ◇ q7) ◇ ((q6 ◇ (q7 ◇ (q6 ◇ q7))) ◇ q4))) = (q5 ◇ q7):=by
    intro q4 q5 q6 q7 q8
    exact ((congrArg (fun t => q5 ◇ t) (congrArg (fun t => t ◇ ((q6 ◇ (q7 ◇ (q6 ◇ q7))) ◇ q4)) (apc0 q4 q8 q6 q7))).symm).trans (((congrArg (fun t => q5 ◇ t) (congrArg (fun t => (q4 ◇ (q8 ◇ ((q6 ◇ (q7 ◇ (q6 ◇ q7))) ◇ (q8 ◇ (q6 ◇ (q7 ◇ (q6 ◇ q7))))))) ◇ t) (congrArg (fun t => (q6 ◇ (q7 ◇ (q6 ◇ q7))) ◇ t) ((h q4 q8 (q6 ◇ (q7 ◇ (q6 ◇ q7)))).symm)))).symm).trans (apc0 q5 (q4 ◇ (q8 ◇ ((q6 ◇ (q7 ◇ (q6 ◇ q7))) ◇ (q8 ◇ (q6 ◇ (q7 ◇ (q6 ◇ q7))))))) q6 q7))
  have apc2 : forall (q9 q10 q11:G), ((q11 ◇ q10) ◇ (q9 ◇ (q10 ◇ (q9 ◇ q10)))) = q11:=by
    intro q9 q10 q11
    exact ((congrArg (fun t => t ◇ (q9 ◇ (q10 ◇ (q9 ◇ q10)))) (apc0 q11 q9 q9 q10)).symm).trans ((h q11 q9 (q9 ◇ (q10 ◇ (q9 ◇ q10)))).symm)
  have apc3 : forall (q12 q13 q14:G), (q12 ◇ (q14 ◇ ((q13 ◇ (q14 ◇ (q13 ◇ q14))) ◇ q14))) = (q12 ◇ q14):=by
    intro q12 q13 q14
    exact ((congrArg (fun t => q12 ◇ t) (apc2 (q13 ◇ (q14 ◇ (q13 ◇ q14))) q14 (q14 ◇ ((q13 ◇ (q14 ◇ (q13 ◇ q14))) ◇ q14)))).symm).trans (apc1 (q14 ◇ ((q13 ◇ (q14 ◇ (q13 ◇ q14))) ◇ q14)) q12 q13 q14 q12)
  have apc4 : forall (q15 q16 q17 q18:G), (q17 ◇ ((q16 ◇ q18) ◇ (((q15 ◇ (q18 ◇ (q15 ◇ q18))) ◇ q18) ◇ q16))) = (q17 ◇ q18):=by
    intro q15 q16 q17 q18
    exact ((congrArg (fun t => q17 ◇ t) (congrArg (fun t => (q16 ◇ q18) ◇ t) (congrArg (fun t => t ◇ q16) (apc3 (q15 ◇ (q18 ◇ (q15 ◇ q18))) q15 q18)))).symm).trans (apc1 q16 q17 (q15 ◇ (q18 ◇ (q15 ◇ q18))) q18 q15)
  have apc6 : forall (q19 q20 q21 q22:G), (q20 ◇ (q19 ◇ (q21 ◇ (q19 ◇ q21)))) = (q20 ◇ q21):=by
    intro q19 q20 q21 q22
    exact ((congrArg (fun t => q20 ◇ t) (apc2 q22 q21 (q19 ◇ (q21 ◇ (q19 ◇ q21))))).symm).trans (((congrArg (fun t => q20 ◇ t) (congrArg (fun t => ((q19 ◇ (q21 ◇ (q19 ◇ q21))) ◇ q21) ◇ t) (apc2 q19 q21 (q22 ◇ (q21 ◇ (q22 ◇ q21)))))).symm).trans (apc4 q22 (q19 ◇ (q21 ◇ (q19 ◇ q21))) q20 q21))
  have apc7 : forall (q23 q24 q25 q26:G), (q24 ◇ ((q23 ◇ q25) ◇ (q25 ◇ q23))) = (q24 ◇ q25):=by
    intro q23 q24 q25 q26
    exact ((congrArg (fun t => q24 ◇ t) (congrArg (fun t => t ◇ (q25 ◇ q23)) (apc6 q26 q23 q25 (q23 ◇ (q26 ◇ (q25 ◇ (q26 ◇ q25))))))).symm).trans (((congrArg (fun t => q24 ◇ t) (congrArg (fun t => (q23 ◇ (q26 ◇ (q25 ◇ (q26 ◇ q25)))) ◇ t) (congrArg (fun t => q25 ◇ t) ((h q23 q26 q25).symm)))).symm).trans (apc6 (q23 ◇ (q26 ◇ (q25 ◇ (q26 ◇ q25)))) q24 q25 q23))
  exact (apc7 z x y (x ◇ y)).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_29404_to_43583 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_29404_to_43583
