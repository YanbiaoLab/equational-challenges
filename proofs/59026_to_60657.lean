-- Equation59026 → Equation60657
-- Recorded verdict: true
-- Premise: (x * y) * z = w * (w * (u * x))
-- Conclusion: (x * y) * z = (z * w) * (x * y)
-- Original submission SHA-256: 530237bcfd465f2e124e800a4dfb998b7e4ceab7db90fcfe9916eff3aa8ecf30
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = w ◇ (w ◇ (u ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = (z ◇ w) ◇ (x ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u:G), ((x ◇ y) ◇ z) = ((x ◇ x) ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x x w u).symm)
  have apc1 : forall (q0 q1 q2 q3:G), ((q1 ◇ q1) ◇ q1) = ((q0 ◇ q0) ◇ q0):=by
    intro q0 q1 q2 q3
    exact ((((apc0 q0 q0 ((q0 ◇ q0) ◇ (q0 ◇ q1)) q0 q0).symm).trans ((h q1 q2 q3 (q0 ◇ q0) q0).symm)).trans (apc0 q1 q2 q3 ((q1 ◇ q2) ◇ q3) ((q1 ◇ q2) ◇ q3))).symm
  have apc3 : forall (q4 q5 q6 q7 q8:G), (((q4 ◇ q4) ◇ q4) ◇ (q4 ◇ q4)) = ((q5 ◇ q5) ◇ q5):=by
    intro q4 q5 q6 q7 q8
    exact ((((congrArg (fun t => t ◇ ((q6 ◇ q6) ◇ q6)) (apc0 q4 q5 (q4 ◇ q5) ((q4 ◇ q5) ◇ (q4 ◇ q5)) ((q4 ◇ q5) ◇ (q4 ◇ q5)))).trans (apc0 (q4 ◇ q4) q4 ((q6 ◇ q6) ◇ q6) (((q4 ◇ q4) ◇ q4) ◇ ((q6 ◇ q6) ◇ q6)) (((q4 ◇ q4) ◇ q4) ◇ ((q6 ◇ q6) ◇ q6)))).trans (congrArg (fun t => t ◇ (q4 ◇ q4)) (apc0 q4 q4 (q4 ◇ q4) ((q4 ◇ q4) ◇ (q4 ◇ q4)) ((q4 ◇ q4) ◇ (q4 ◇ q4))))).symm).trans ((((congrArg (fun t => ((q4 ◇ q5) ◇ (q4 ◇ q5)) ◇ t) (apc1 q6 (q4 ◇ q5) q6 q6)).symm).trans ((h q5 q7 q8 ((q4 ◇ q5) ◇ (q4 ◇ q5)) q4).symm)).trans (apc0 q5 q7 q8 ((q5 ◇ q7) ◇ q8) ((q5 ◇ q7) ◇ q8)))
  have apc6 : forall (q9 q10 q11:G), (((q9 ◇ q9) ◇ q9) ◇ (q10 ◇ q10)) = ((q11 ◇ q11) ◇ q11):=by
    intro q9 q10 q11
    exact ((congrArg (fun t => t ◇ (q10 ◇ q10)) (apc1 q9 q10 q9 q9)).symm).trans (apc3 q10 q11 q9 q9 q9)
  have apc7 : forall (q12 q13 q14 q15:G), ((q15 ◇ q15) ◇ q15) = ((q14 ◇ q12) ◇ q13):=by
    intro q12 q13 q14 q15
    exact ((h q14 q12 q13 ((q14 ◇ q14) ◇ q14) (q14 ◇ q14)).trans (apc6 q14 ((q14 ◇ q14) ◇ q14) q15)).symm
  exact ((apc7 y z x ((x ◇ y) ◇ z)).symm).trans (apc7 w (x ◇ y) z ((x ◇ y) ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_59026_to_60657 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_59026_to_60657
