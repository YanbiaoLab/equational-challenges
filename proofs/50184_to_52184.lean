-- Equation50184 → Equation52184
-- Recorded verdict: true
-- Premise: x * y = (z * (w * (y * x))) * x
-- Conclusion: x * x = ((y * (z * x)) * y) * y
-- Original submission SHA-256: ea3c9f2dc56d82c19bc8060638ffb901c021db4df6a7530648892319cc36cfe2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (w ◇ (y ◇ x))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ (z ◇ x)) ◇ y) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (((q1 ◇ (q3 ◇ q2)) ◇ q0) ◇ q2) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q2) ((h (q1 ◇ (q3 ◇ q2)) q0 q0 q0).symm)).symm).trans ((h q2 q3 (q0 ◇ (q0 ◇ (q0 ◇ (q1 ◇ (q3 ◇ q2))))) q1).symm)
  have apc1 : forall (q4 q5 q6:G), (q5 ◇ q6) = (q5 ◇ q4):=by
    intro q4 q5 q6
    exact (((apc0 (q4 ◇ (q6 ◇ q5)) q4 q5 q4).symm).trans ((h q5 q6 (q4 ◇ (q4 ◇ q5)) q4).symm)).symm
  have apc3 : forall (q7 q8 q9 q10:G), ((q8 ◇ q7) ◇ q9) = (q9 ◇ q10):=by
    intro q7 q8 q9 q10
    exact ((congrArg (fun t => t ◇ q9) (apc0 (q10 ◇ q9) q7 q8 q7)).symm).trans (apc0 q8 (q7 ◇ (q7 ◇ q8)) q9 q10)
  have apc4 : forall (q11 q12 q13 q14 q15:G), ((q12 ◇ q11) ◇ q14) = (q15 ◇ q13):=by
    intro q11 q12 q13 q14 q15
    exact (((apc3 q11 q12 q15 q13).symm).trans (apc1 q14 (q12 ◇ q11) q15)).symm
  have apc5 : forall (q11 q12 q13 q14 q15:G), (q15 ◇ q13) = (q11 ◇ q11):=by
    intro q11 q12 q13 q14 q15
    exact ((apc4 q11 q11 q13 q11 q15).symm).trans (apc4 q11 q11 q11 q11 q11)
  exact (apc5 (x ◇ x) (x ◇ x) x (x ◇ x) x).trans ((apc5 (x ◇ x) (x ◇ x) y (x ◇ x) ((y ◇ (z ◇ x)) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50184_to_52184 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_50184_to_52184
