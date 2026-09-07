-- Equation47573 → Equation49117
-- Recorded verdict: true
-- Premise: x * y = (z * w) * ((y * u) * x)
-- Conclusion: x * y = ((z * x) * w) * (w * y)
-- Original submission SHA-256: eb8aaa017952e45ed2be929869b43d254ef25751c10a0a0d097219526010ed82
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ w) ◇ ((y ◇ u) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ x) ◇ w) ◇ (w ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), (((q2 ◇ q0) ◇ q1) ◇ q4) = ((q5 ◇ q3) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2 q3 q4 q5
    exact (((congrArg (fun t => (q5 ◇ q3) ◇ t) ((h q1 q2 q4 q0 q0).symm)).symm).trans ((h ((q2 ◇ q0) ◇ q1) q4 q5 q3 q0).symm)).symm
  have apc1 : forall (q6 q7 q8 q9 q10 q11:G), ((q8 ◇ q7) ◇ (q9 ◇ q6)) = (q10 ◇ q11):=by
    intro q6 q7 q8 q9 q10 q11
    exact ((apc0 q6 q9 q6 q7 ((q11 ◇ q6) ◇ q10) q8).symm).trans ((h q10 q11 (q6 ◇ q6) q9 q6).symm)
  have apc2 : forall (q12 q13 q14 q15:G), (q14 ◇ q15) = (q12 ◇ q13):=by
    intro q12 q13 q14 q15
    exact (((apc1 q12 q12 q12 q12 q12 q13).symm).trans (apc1 q12 q12 q12 q12 q14 q15)).symm
  exact (apc2 (x ◇ y) (((z ◇ x) ◇ w) ◇ (w ◇ y)) x y).trans ((apc2 (x ◇ y) (((z ◇ x) ◇ w) ◇ (w ◇ y)) ((z ◇ x) ◇ w) (w ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47573_to_49117 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47573_to_49117
