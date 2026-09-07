-- Equation48461 → Equation57891
-- Recorded verdict: true
-- Premise: x * y = (z * (w * z)) * (y * x)
-- Conclusion: x * (y * z) = ((x * w) * u) * x
-- Original submission SHA-256: 9c9dc9c45920148cb455710459f05fbb45d5c8f7c33c1d5c149ef007c0967d90
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (w ◇ z)) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = ((x ◇ w) ◇ u) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), ((q5 ◇ (q4 ◇ q5)) ◇ (q1 ◇ q2)) = ((q2 ◇ q1) ◇ (q3 ◇ (q0 ◇ q3))):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => (q5 ◇ (q4 ◇ q5)) ◇ t) ((h q1 q2 q3 q0).symm)).symm).trans ((h (q2 ◇ q1) (q3 ◇ (q0 ◇ q3)) q5 q4).symm)
  have apc1 : forall (q6 q7 q8 q9:G), ((q8 ◇ q9) ◇ (q7 ◇ (q6 ◇ q7))) = (q8 ◇ q9):=by
    intro q6 q7 q8 q9
    exact ((apc0 q6 q9 q8 q7 q6 q6).symm).trans ((h q8 q9 q6 q6).symm)
  have apc2 : forall (q10 q11 q12 q13:G), (q13 ◇ (q11 ◇ q13)) = ((q10 ◇ q12) ◇ q12):=by
    intro q10 q11 q12 q13
    exact ((apc1 q10 q12 q13 (q11 ◇ q13)).symm).trans ((h (q10 ◇ q12) q12 q13 q11).symm)
  have apc3 : forall (q14 q15 q16 q17:G), (q15 ◇ (q14 ◇ q15)) = (q16 ◇ q17):=by
    intro q14 q15 q16 q17
    exact (apc2 q16 q14 (q17 ◇ q16) q15).trans ((h q16 q17 q16 q17).symm)
  have apc6 : forall (q14 q16 q17 q15:G), (q16 ◇ q17) = (q14 ◇ q14):=by
    intro q14 q16 q17 q15
    exact ((apc3 q14 q15 q16 q17).symm).trans (apc3 q14 q15 q14 q14)
  exact (apc6 (x ◇ (y ◇ z)) x (y ◇ z) (x ◇ (y ◇ z))).trans ((apc6 (x ◇ (y ◇ z)) ((x ◇ w) ◇ u) x (x ◇ (y ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48461_to_57891 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48461_to_57891
