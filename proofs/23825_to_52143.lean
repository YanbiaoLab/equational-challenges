-- Equation23825 → Equation52143
-- Recorded verdict: true
-- Premise: x = ((y ◇ z) ◇ z) ◇ (w ◇ (x ◇ w))
-- Conclusion: x ◇ x = ((y ◇ (y ◇ x)) ◇ x) ◇ y
-- Original submission SHA-256: afdb0a12bd9c6c2bdfab0f4b5fbd56712067d7930953e8597edcadfdfb9776a8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ z) ◇ (w ◇ (x ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = ((y ◇ (y ◇ x)) ◇ x) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3:G), (((q2 ◇ q3) ◇ q3) ◇ (q0 ◇ q1)) = q1:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => ((q2 ◇ q3) ◇ q3) ◇ t) ((h (q0 ◇ q1) q0 q1 q1).symm)).symm).trans ((h q1 q2 q3 ((q0 ◇ q1) ◇ q1)).symm)
  have apc1 : forall (q4 q5 q6 q7:G), (((q6 ◇ q7) ◇ q7) ◇ q5) = (q4 ◇ q5):=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => ((q6 ◇ q7) ◇ q7) ◇ t) (apc0 q4 q5 q4 q4)).symm).trans (apc0 ((q4 ◇ q4) ◇ q4) (q4 ◇ q5) q6 q7)
  have apc4 : forall (q8 q9 q10 q11 q12 q13:G), ((q9 ◇ q10) ◇ q10) = (q8 ◇ q11):=by
    intro q8 q9 q10 q11 q12 q13
    exact (((apc0 q11 (q8 ◇ q11) q12 q13).symm).trans (((congrArg (fun t => ((q12 ◇ q13) ◇ q13) ◇ t) (congrArg (fun t => q11 ◇ t) (apc1 q8 q11 q9 q10))).symm).trans ((h ((q9 ◇ q10) ◇ q10) q12 q13 q11).symm))).symm
  exact ((apc4 x (x ◇ x) x x (x ◇ x) (x ◇ x)).symm).trans (apc4 ((y ◇ (y ◇ x)) ◇ x) (x ◇ x) x y (x ◇ x) (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23825_to_52143 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_23825_to_52143
