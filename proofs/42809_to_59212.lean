-- Equation42809 → Equation59212
-- Recorded verdict: true
-- Premise: x * y = y * (y * ((y * x) * z))
-- Conclusion: (x * x) * y = z * ((y * x) * x)
-- Original submission SHA-256: 9d5dae7ad132b9759c701033915f07ef0462c9b97600f8f22088d806860084b4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (y ◇ ((y ◇ x) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ y = z ◇ ((y ◇ x) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ (q2 ◇ (q0 ◇ (q2 ◇ q1)))) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => q2 ◇ t) ((h q0 (q2 ◇ q1) q0).symm))).symm).trans ((h q1 q2 ((q2 ◇ q1) ◇ (((q2 ◇ q1) ◇ q0) ◇ q0))).symm)
  have apc1 : forall (q3 q4:G), (q4 ◇ (q3 ◇ q4)) = ((q4 ◇ q3) ◇ q4):=by
    intro q3 q4
    exact ((congrArg (fun t => q4 ◇ t) (apc0 q4 q3 q4)).symm).trans (apc0 q4 (q4 ◇ q3) q4)
  have apc2 : forall (q5 q6 q7:G), (q6 ◇ q7) = (q5 ◇ q7):=by
    intro q5 q6 q7
    exact (((apc0 (q7 ◇ q6) q5 q7).symm).trans ((h q6 q7 (q7 ◇ q5)).symm)).symm
  have apc3 : forall (q8 q9 q10:G), (q8 ◇ (q9 ◇ q10)) = ((q10 ◇ q9) ◇ q10):=by
    intro q8 q9 q10
    exact ((apc2 q8 q10 (q9 ◇ q10)).symm).trans (apc1 q9 q10)
  have apc4 : forall (q11 q12 q13:G), (((q11 ◇ q12) ◇ q11) ◇ q13) = (q11 ◇ q12):=by
    intro q11 q12 q13
    exact (((apc3 (((q12 ◇ q11) ◇ q13) ◇ q12) (q12 ◇ q11) q13).trans (congrArg (fun t => t ◇ q13) (apc3 q13 q12 q11))).symm).trans (((apc3 q12 q12 ((q12 ◇ q11) ◇ q13)).symm).trans ((h q11 q12 q13).symm))
  have apc5 : forall (q14 q15 q16 q17:G), ((q17 ◇ q16) ◇ q17) = (q14 ◇ q15):=by
    intro q14 q15 q16 q17
    exact (((apc4 q14 q15 (q16 ◇ q17)).symm).trans (apc3 ((q14 ◇ q15) ◇ q14) q16 q17)).symm
  exact ((apc5 (x ◇ x) y (z ◇ ((y ◇ x) ◇ x)) ((x ◇ x) ◇ y)).symm).trans (apc5 z ((y ◇ x) ◇ x) (z ◇ ((y ◇ x) ◇ x)) ((x ◇ x) ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42809_to_59212 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42809_to_59212
