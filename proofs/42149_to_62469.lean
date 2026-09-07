-- Equation42149 → Equation62469
-- Recorded verdict: true
-- Premise: x * y = z * (y * (z * (y * x)))
-- Conclusion: (x * y) * z = ((w * y) * y) * z
-- Original submission SHA-256: 1bf38519ec6798fd8b19edbd28d9da49e98fbec4fca5d3df8bcf046e95be8eb0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ (y ◇ (z ◇ (y ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = ((w ◇ y) ◇ y) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ q2)) = ((q2 ◇ q0) ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) ((h q0 q2 q1).symm)).symm).trans ((h (q2 ◇ q0) q1 q2).symm)
  have apc1 : forall (q3 q4 q5 q6:G), ((q6 ◇ q4) ◇ q5) = ((q6 ◇ q4) ◇ q3):=by
    intro q3 q4 q5 q6
    exact (((apc0 q4 q3 q6).symm).trans (apc0 q4 q5 q6)).symm
  have apc2 : forall (q7 q8 q9 q10 q11:G), (((q9 ◇ q8) ◇ q10) ◇ q11) = ((q9 ◇ q8) ◇ q7):=by
    intro q7 q8 q9 q10 q11
    exact (((apc1 q7 q8 (q10 ◇ (q9 ◇ q8)) q9).symm).trans (apc0 q10 q11 (q9 ◇ q8))).symm
  have apc3 : forall (q0 q1 q2:G), ((q2 ◇ q0) ◇ q1) = ((q2 ◇ q0) ◇ q0):=by
    intro q0 q1 q2
    exact ((apc0 q0 q1 q2).symm).trans (apc0 q0 q0 q2)
  have apc7 : forall (q12 q13 q14 q15 q16 q17:G), ((q16 ◇ q15) ◇ q14) = ((q12 ◇ q13) ◇ q13):=by
    intro q12 q13 q14 q15 q16 q17
    exact (((apc3 q13 q17 q12).symm).trans (((congrArg (fun t => t ◇ q17) ((h q12 q13 (q16 ◇ q15)).symm)).symm).trans (apc2 q14 q15 q16 (q13 ◇ ((q16 ◇ q15) ◇ (q13 ◇ q12))) q17))).symm
  exact (apc7 (((w ◇ y) ◇ y) ◇ z) ((x ◇ y) ◇ z) z y x ((x ◇ y) ◇ z)).trans ((apc7 (((w ◇ y) ◇ y) ◇ z) ((x ◇ y) ◇ z) z y (w ◇ y) ((x ◇ y) ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42149_to_62469 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42149_to_62469
