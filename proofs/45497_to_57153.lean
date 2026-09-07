-- Equation45497 → Equation57153
-- Recorded verdict: true
-- Premise: x * y = y * (((z * y) * w) * w)
-- Conclusion: x * (y * z) = (z * (w * y)) * x
-- Original submission SHA-256: 8bee341ac0a0ccf99609ae5db8d18d84bec446556f46638192f91ff37b2a4075
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (((z ◇ y) ◇ w) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (z ◇ (w ◇ y)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ q0)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) ((apc0 ((q0 ◇ q2) ◇ q0) q0 q0 q0).symm)).symm).trans ((h q1 q2 q0 q0).symm)
  have apc2 : forall (q3 q4 q5 q6:G), (q6 ◇ (q3 ◇ q4)) = (q5 ◇ q6):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => q6 ◇ t) (apc0 q3 q4 q3 q3)).symm).trans (apc1 q4 q5 q6)
  have apc3 : forall (q7 q8 q9:G), (q9 ◇ (q7 ◇ q8)) = (q9 ◇ q9):=by
    intro q7 q8 q9
    exact (apc2 q7 q8 q7 q9).trans ((apc0 q7 q9 q7 q7).symm)
  have apc4 : forall (q10 q11 q12:G), (q11 ◇ q12) = (q10 ◇ q12):=by
    intro q10 q11 q12
    exact ((h q10 q12 q10 q10).trans ((h q11 q12 q10 q10).symm)).symm
  have apc5 : forall (q13 q14 q15 q16 q17:G), (q14 ◇ q15) = (q13 ◇ q13):=by
    intro q13 q14 q15 q16 q17
    exact (((apc3 ((q16 ◇ q15) ◇ q17) q17 q13).symm).trans (((apc4 q13 q15 (((q16 ◇ q15) ◇ q17) ◇ q17)).symm).trans ((h q14 q15 q16 q17).symm))).symm
  exact (apc5 (x ◇ (y ◇ z)) x (y ◇ z) (x ◇ (y ◇ z)) (x ◇ (y ◇ z))).trans ((apc5 (x ◇ (y ◇ z)) (z ◇ (w ◇ y)) x (x ◇ (y ◇ z)) (x ◇ (y ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45497_to_57153 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45497_to_57153
