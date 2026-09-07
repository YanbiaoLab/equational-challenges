-- Equation49124 → Equation41914
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * w) * (u * w)
-- Conclusion: x * y = y * (x * (z * (z * w)))
-- Original submission SHA-256: 422b02d414d6b9d541f01b299bac613f9cc4d38847c3861afe76001ab205c67c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ x) ◇ w) ◇ (u ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (x ◇ (z ◇ (z ◇ w)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc1 : forall (q0 q1 q2 q3 q4 q5:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1 q2 q3 q4 q5
    exact (((((congrArg (fun t => (q0 ◇ q2) ◇ t) (congrArg (fun t => q3 ◇ t) (apc0 q4 q1 (q4 ◇ q1) (q4 ◇ q1) (q4 ◇ q1)))).trans (congrArg (fun t => t ◇ (q3 ◇ (q4 ◇ q4))) (apc0 q0 q2 (q0 ◇ q2) (q0 ◇ q2) (q0 ◇ q2)))).trans (congrArg (fun t => (q0 ◇ q0) ◇ t) (apc0 q3 (q4 ◇ q4) (q3 ◇ (q4 ◇ q4)) (q3 ◇ (q4 ◇ q4)) (q3 ◇ (q4 ◇ q4))))).trans (apc0 (q0 ◇ q0) (q3 ◇ q3) ((q0 ◇ q0) ◇ (q3 ◇ q3)) ((q0 ◇ q0) ◇ (q3 ◇ q3)) ((q0 ◇ q0) ◇ (q3 ◇ q3)))).symm).trans ((((congrArg (fun t => t ◇ (q3 ◇ (q4 ◇ q1))) ((h q0 q2 q4 q1 q4).symm)).symm).trans ((h q1 q5 (q4 ◇ q0) (q4 ◇ q1) q3).symm)).trans (apc0 q1 q5 (q1 ◇ q5) (q1 ◇ q5) (q1 ◇ q5)))
  have apc2 : forall (q4 q0 q2 q3 q1 q5:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q4 q0 q2 q3 q1 q5
    exact ((apc1 q0 q1 q2 q3 q4 q5).symm).trans (apc1 q0 q0 q2 q3 q4 q5)
  have apc4 : forall (x y z w u:G), (((z ◇ x) ◇ w) ◇ (u ◇ u)) = (((x ◇ x) ◇ x) ◇ (x ◇ x)):=by
    intro x y z w u
    exact ((congrArg (fun t => ((z ◇ x) ◇ w) ◇ t) (apc0 u w (u ◇ w) (u ◇ w) (u ◇ w))).symm).trans (((h x y z w u).symm).trans (h x y x x x))
  have apc5 : forall (q6 q7:G), (((q7 ◇ q7) ◇ q7) ◇ (q7 ◇ q7)) = (q7 ◇ q6):=by
    intro q6 q7
    exact ((h q7 q6 q6 q6 q6).trans (apc4 q7 q6 q6 q6 q6)).symm
  have apc6 : forall (q8 q9 q10:G), (q10 ◇ q9) = (q10 ◇ q8):=by
    intro q8 q9 q10
    exact ((h q10 q8 q10 q10 q10).trans (apc5 q9 q10)).symm
  have apc7 : forall (q11 q12 q13:G), (q13 ◇ q11) = (q12 ◇ q12):=by
    intro q11 q12 q13
    exact ((apc6 q11 q13 q13).symm).trans (apc2 q11 q12 q11 q11 q13 q11)
  exact (apc7 y (x ◇ y) x).trans ((apc7 (x ◇ (z ◇ (z ◇ w))) (x ◇ y) y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49124_to_41914 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49124_to_41914
