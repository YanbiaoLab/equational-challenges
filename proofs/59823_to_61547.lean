-- Equation59823 → Equation61547
-- Recorded verdict: true
-- Premise: (x * y) * z = w * ((x * w) * w)
-- Conclusion: (x * y) * z = (z * (w * z)) * u
-- Original submission SHA-256: 13a46ac936ad7292932241c280b475e34b4d555144142379317c0a9defcb8f13
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = w ◇ ((x ◇ w) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = (z ◇ (w ◇ z)) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z w:G), ((x ◇ y) ◇ z) = ((x ◇ x) ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x x w).symm)
  have apc1 : forall (q0 q1 q2 q3:G), ((q1 ◇ q1) ◇ q1) = ((q0 ◇ q0) ◇ q0):=by
    intro q0 q1 q2 q3
    exact ((((apc0 q0 q0 ((q1 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) q0).symm).trans ((h q1 q2 q3 (q0 ◇ q0)).symm)).trans (apc0 q1 q2 q3 ((q1 ◇ q2) ◇ q3))).symm
  have apc4 : forall (x y z w:G), (x ◇ ((x ◇ x) ◇ x)) = (w ◇ ((x ◇ w) ◇ w)):=by
    intro x y z w
    exact (((h x y z w).symm).trans (h x y z x)).symm
  have apc11 : forall (q4 q5 q6:G), (q6 ◇ ((q6 ◇ q6) ◇ q6)) = ((q6 ◇ q4) ◇ q5):=by
    intro q4 q5 q6
    exact ((h q6 q4 q5 q4).trans ((apc4 q6 q4 q4 q4).symm)).symm
  have apc12 : forall (q7 q8 q9 q10 q11:G), ((q11 ◇ q9) ◇ q10) = ((q11 ◇ q7) ◇ q8):=by
    intro q7 q8 q9 q10 q11
    exact ((h q11 q7 q8 q11).trans (apc11 q9 q10 q11)).symm
  have apc14 : forall (q12 q13 q14 q15:G), ((q15 ◇ q12) ◇ q13) = ((q14 ◇ q14) ◇ q14):=by
    intro q12 q13 q14 q15
    exact ((apc12 q12 q13 q15 q15 q15).symm).trans (apc1 q14 q15 q12 q12)
  exact (apc14 y z ((x ◇ y) ◇ z) x).trans ((apc14 (w ◇ z) u ((x ◇ y) ◇ z) z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_59823_to_61547 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_59823_to_61547
