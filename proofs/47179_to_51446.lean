-- Equation47179 → Equation51446
-- Recorded verdict: true
-- Premise: x * y = (y * x) * ((z * w) * z)
-- Conclusion: x * y = ((x * y) * (z * z)) * z
-- Original submission SHA-256: 85901344c2fe77948774cf659c823f6b4fc615450c5ceb255d7ba30ae5968501
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ x) ◇ ((z ◇ w) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((x ◇ y) ◇ (z ◇ z)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), ((q3 ◇ q2) ◇ ((q0 ◇ q1) ◇ (q1 ◇ q0))) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => (q3 ◇ q2) ◇ t) (congrArg (fun t => t ◇ (q1 ◇ q0)) ((h q0 q1 q0 q0).symm))).symm).trans ((h q2 q3 (q1 ◇ q0) ((q0 ◇ q0) ◇ q0)).symm)
  have apc2 : forall (q4 q5 q6 q7 q8 q9:G), (((q7 ◇ q4) ◇ q7) ◇ (q6 ◇ q5)) = (q6 ◇ q5):=by
    intro q4 q5 q6 q7 q8 q9
    exact (((apc0 q8 q9 q6 q5).symm).trans (((congrArg (fun t => t ◇ ((q8 ◇ q9) ◇ (q9 ◇ q8))) ((h q5 q6 q7 q4).symm)).symm).trans (apc0 q8 q9 ((q7 ◇ q4) ◇ q7) (q6 ◇ q5)))).symm
  have apc4 : forall (q10 q11 q12 q13 q14 q15:G), (((q12 ◇ q11) ◇ ((q13 ◇ q10) ◇ q13)) ◇ (q15 ◇ q14)) = (q15 ◇ q14):=by
    intro q10 q11 q12 q13 q14 q15
    exact ((congrArg (fun t => t ◇ (q15 ◇ q14)) (congrArg (fun t => t ◇ ((q13 ◇ q10) ◇ q13)) (apc2 q10 q11 q12 q13 q10 q10))).symm).trans (apc2 (q12 ◇ q11) q14 q15 ((q13 ◇ q10) ◇ q13) q10 q10)
  have apc7 : forall (q16 q17 q18 q19 q20 q21:G), ((q19 ◇ q18) ◇ q19) = (q17 ◇ q16):=by
    intro q16 q17 q18 q19 q20 q21
    exact (((apc4 q20 q16 q17 q21 q19 (q19 ◇ q18)).symm).trans ((h ((q21 ◇ q20) ◇ q21) (q17 ◇ q16) q19 q18).symm)).trans (apc2 q20 q16 q17 q21 (((q21 ◇ q20) ◇ q21) ◇ (q17 ◇ q16)) (((q21 ◇ q20) ◇ q21) ◇ (q17 ◇ q16)))
  exact ((apc7 y x (((x ◇ y) ◇ (z ◇ z)) ◇ z) (x ◇ y) (x ◇ y) (x ◇ y)).symm).trans (apc7 z ((x ◇ y) ◇ (z ◇ z)) (((x ◇ y) ◇ (z ◇ z)) ◇ z) (x ◇ y) (x ◇ y) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47179_to_51446 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47179_to_51446
