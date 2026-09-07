-- Equation25433 → Equation48041
-- Recorded verdict: true
-- Premise: x = (y * (z * (x * w))) * (z * y)
-- Conclusion: x * y = (y * (x * y)) * (z * w)
-- Original submission SHA-256: 0f2035cc8d2b9f640ff5e68d1056ad175d923956b8f85bcc03dedbd1e03d6468
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ (x ◇ w))) ◇ (z ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ (x ◇ y)) ◇ (z ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), ((q4 ◇ (q5 ◇ q1)) ◇ (q5 ◇ q4)) = (q2 ◇ (q3 ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => t ◇ (q5 ◇ q4)) (congrArg (fun t => q4 ◇ t) (congrArg (fun t => q5 ◇ t) ((h q1 q2 q3 q0).symm)))).symm).trans ((h (q2 ◇ (q3 ◇ (q1 ◇ q0))) q4 q5 (q3 ◇ q2)).symm)
  have apc1 : forall (q6 q7 q8 q9 q10 q11 q12:G), (q11 ◇ (q12 ◇ (q10 ◇ q9))) = (q7 ◇ (q8 ◇ (q10 ◇ q6))):=by
    intro q6 q7 q8 q9 q10 q11 q12
    exact (((apc0 q6 q10 q7 q8 q6 q6).symm).trans (apc0 q9 q10 q11 q12 q6 q6)).symm
  have apc2 : forall (q13 q14 q15 q16 q17:G), (q14 ◇ (q15 ◇ (q16 ◇ q13))) = q17:=by
    intro q13 q14 q15 q16 q17
    exact ((apc1 q13 q14 q15 q13 q16 ((q16 ◇ q13) ◇ (q13 ◇ (q17 ◇ q13))) q13).symm).trans ((h q17 (q16 ◇ q13) q13 q13).symm)
  have apc3 : forall (q13 q17 q14 q15 q16:G), q17 = q13:=by
    intro q13 q17 q14 q15 q16
    exact ((apc2 q13 q14 q15 q16 q17).symm).trans (apc2 q13 q14 q15 q16 q13)
  exact (apc3 (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y)).trans ((apc3 (x ◇ y) ((y ◇ (x ◇ y)) ◇ (z ◇ w)) (x ◇ y) (x ◇ y) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_25433_to_48041 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_25433_to_48041
