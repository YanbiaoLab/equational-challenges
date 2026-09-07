-- Equation60638 → Equation61612
-- Recorded verdict: true
-- Premise: (x * y) * z = (z * y) * (w * u)
-- Conclusion: (x * y) * z = (w * (z * x)) * y
-- Original submission SHA-256: 34547f438d8c3b470a4e49e66f516bb25a67efca39e9f02f5f9c50e8ac6f157e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = (z ◇ y) ◇ (w ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = (w ◇ (z ◇ x)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u:G), ((y ◇ y) ◇ z) = ((x ◇ y) ◇ z):=by
    intro x y z w u
    exact ((h x y z x x).trans ((h y y z x x).symm)).symm
  have apc4 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q4) ◇ (q2 ◇ q1)) = ((q3 ◇ q4) ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((apc0 q0 q4 (q2 ◇ q1) q0 q0).symm).trans ((h q3 q4 q4 q2 q1).symm)
  have apc6 : forall (q5 q6 q7 q8:G), ((q6 ◇ q7) ◇ q8) = ((q5 ◇ q7) ◇ q7):=by
    intro q5 q6 q7 q8
    exact (((apc4 q8 q5 q5 q5 q7).symm).trans ((h q6 q7 q8 q5 q5).symm)).symm
  have apc20 : forall (q1 q2 q4 q9:G), ((q9 ◇ q4) ◇ (q2 ◇ q1)) = ((q4 ◇ q4) ◇ q9):=by
    intro q1 q2 q4 q9
    exact ((apc0 q1 q4 q9 q1 q1).trans (h q1 q4 q9 q2 q1)).symm
  have apc21 : forall (q10 q11:G), ((q11 ◇ q11) ◇ q11) = ((q10 ◇ q10) ◇ q10):=by
    intro q10 q11
    exact ((((apc20 q10 q10 q10 (q10 ◇ q10)).trans (apc20 q10 q10 q10 q10)).symm).trans ((((congrArg (fun t => t ◇ (q10 ◇ q10)) (apc6 q10 q10 q10 q11)).symm).trans (apc20 q10 q10 q11 (q10 ◇ q10))).trans (apc20 q10 q10 q11 q11))).symm
  have apc23 : forall (q12 q13 q14 q15:G), ((q13 ◇ q14) ◇ q15) = ((q12 ◇ q12) ◇ q12):=by
    intro q12 q13 q14 q15
    exact (((apc21 q12 q14).symm).trans ((apc6 q14 q13 q14 q15).symm)).symm
  exact (apc23 ((x ◇ y) ◇ z) x y z).trans ((apc23 ((x ◇ y) ◇ z) w (z ◇ x) y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_60638_to_61612 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_60638_to_61612
