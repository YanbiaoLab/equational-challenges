-- Equation42341 → Equation53854
-- Recorded verdict: true
-- Premise: x * y = z * (w * (z * (u * u)))
-- Conclusion: x * (x * x) = y * (z * (w * x))
-- Original submission SHA-256: 23066352be75c18dd2c6a647b0e792a5b121ef245d1447bc8fdd581cff2de4bb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (w ◇ (z ◇ (u ◇ u)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ x) = y ◇ (z ◇ (w ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), (q5 ◇ (q2 ◇ (q0 ◇ q1))) = (q3 ◇ q4):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => q5 ◇ t) (congrArg (fun t => q2 ◇ t) ((h q0 q1 q5 (q5 ◇ (q0 ◇ q0)) q0).symm))).symm).trans ((h q3 q4 q5 q2 (q5 ◇ (q0 ◇ q0))).symm)
  have apc1 : forall (q0 q1 q2 q3 q4 q5:G), (q5 ◇ (q2 ◇ (q0 ◇ q1))) = (q3 ◇ (q3 ◇ (q3 ◇ q3))):=by
    intro q0 q1 q2 q3 q4 q5
    exact (apc0 q0 q1 q2 q3 q4 q5).trans ((apc0 q3 q3 q3 q3 q4 q3).symm)
  have apc2 : forall (q6 q7 q8 q9:G), (q8 ◇ (q8 ◇ (q8 ◇ q8))) = (q9 ◇ (q6 ◇ q7)):=by
    intro q6 q7 q8 q9
    exact (((congrArg (fun t => q9 ◇ t) (apc0 q6 q6 q6 q6 q7 q6)).symm).trans (apc1 q6 (q6 ◇ q6) q6 q8 q6 q9)).symm
  exact ((apc2 x x (x ◇ (x ◇ x)) x).symm).trans (apc2 z (w ◇ x) (x ◇ (x ◇ x)) y)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42341_to_53854 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42341_to_53854
