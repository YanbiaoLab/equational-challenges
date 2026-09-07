-- Equation50829 → Equation51497
-- Recorded verdict: true
-- Premise: x * y = (z * ((x * y) * z)) * x
-- Conclusion: x * y = ((x * z) * (z * z)) * z
-- Original submission SHA-256: 6d793f91f85f47c424c15e19aebce86176d0539fbe83a99f7d915b5b35d73ba5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ ((x ◇ y) ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((x ◇ z) ◇ (z ◇ z)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ ((q2 ◇ q0) ◇ q1)) = ((q2 ◇ (q2 ◇ q0)) ◇ q1):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => t ◇ q1) (congrArg (fun t => q2 ◇ t) ((h q2 q0 q1).symm))).symm).trans ((h q1 ((q2 ◇ q0) ◇ q1) q2).symm)).symm
  have apc1 : forall (q3 q4 q5:G), (((q3 ◇ (q3 ◇ q4)) ◇ q5) ◇ q3) = (q3 ◇ q4):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => t ◇ q3) (apc0 q4 q5 q3)).symm).trans ((h q3 q4 q5).symm)
  have apc2 : forall (q6 q7 q8:G), (q7 ◇ q8) = (q7 ◇ q6):=by
    intro q6 q7 q8
    exact (((apc1 q7 q6 ((q7 ◇ q8) ◇ (q7 ◇ (q7 ◇ q6)))).symm).trans ((h q7 q8 (q7 ◇ (q7 ◇ q6))).symm)).symm
  have apc6 : forall (q9 q10 q11 q12:G), ((q12 ◇ q9) ◇ q10) = (q10 ◇ q11):=by
    intro q9 q10 q11 q12
    exact ((congrArg (fun t => t ◇ q10) (apc2 q9 q12 ((q10 ◇ q11) ◇ q12))).symm).trans ((h q10 q11 q12).symm)
  have apc7 : forall (q13 q14 q15 q16 q17:G), ((q15 ◇ q13) ◇ q16) = (q17 ◇ q14):=by
    intro q13 q14 q15 q16 q17
    exact (((apc6 q13 q17 q14 q15).symm).trans (apc2 q16 (q15 ◇ q13) q17)).symm
  have apc8 : forall (q18 q19 q20 q21:G), (q20 ◇ q21) = (q19 ◇ q18):=by
    intro q18 q19 q20 q21
    exact (((apc7 ((q20 ◇ q21) ◇ q18) q18 q18 q20 q19).symm).trans ((h q20 q21 q18).symm)).symm
  exact (apc8 (x ◇ y) (((x ◇ z) ◇ (z ◇ z)) ◇ z) x y).trans ((apc8 (x ◇ y) (((x ◇ z) ◇ (z ◇ z)) ◇ z) ((x ◇ z) ◇ (z ◇ z)) z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50829_to_51497 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_50829_to_51497
