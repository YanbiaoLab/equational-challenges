-- Equation47379 → Equation42752
-- Recorded verdict: true
-- Premise: x * y = (z * y) * ((x * y) * z)
-- Conclusion: x * y = x * (z * ((w * w) * w))
-- Original submission SHA-256: e0a8f94050119400bf57737989b3dc5baf3c7ba1b3818f91d9e7ba0351272ea8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ y) ◇ ((x ◇ y) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = x ◇ (z ◇ ((w ◇ w) ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((((q0 ◇ q2) ◇ q1) ◇ q2) ◇ (q0 ◇ q2)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (((q0 ◇ q2) ◇ q1) ◇ q2) ◇ t) ((h q0 q2 q1).symm)).symm).trans ((h q1 q2 ((q0 ◇ q2) ◇ q1)).symm)
  have apc1 : forall (q3 q4 q5 q6:G), ((q6 ◇ (q3 ◇ q5)) ◇ ((q4 ◇ q5) ◇ q6)) = (q4 ◇ q5):=by
    intro q3 q4 q5 q6
    exact (((congrArg (fun t => (q6 ◇ (q3 ◇ q5)) ◇ t) (congrArg (fun t => t ◇ q6) (apc0 q3 q4 q5))).symm).trans ((h (((q3 ◇ q5) ◇ q4) ◇ q5) (q3 ◇ q5) q6).symm)).trans (apc0 q3 q4 q5)
  have apc2 : forall (q7 q8 q9 q10:G), ((q7 ◇ q8) ◇ ((q9 ◇ q10) ◇ (q10 ◇ q8))) = (q9 ◇ q10):=by
    intro q7 q8 q9 q10
    exact ((congrArg (fun t => t ◇ ((q9 ◇ q10) ◇ (q10 ◇ q8))) ((h q7 q8 q10).symm)).symm).trans (apc1 (q7 ◇ q8) q9 q10 (q10 ◇ q8))
  have apc3 : forall (q11 q12 q13 q14 q15:G), ((q14 ◇ q15) ◇ ((q12 ◇ q13) ◇ ((q11 ◇ q13) ◇ q15))) = (q12 ◇ q13):=by
    intro q11 q12 q13 q14 q15
    exact (((congrArg (fun t => (q14 ◇ q15) ◇ t) (congrArg (fun t => t ◇ ((q11 ◇ q13) ◇ q15)) (apc0 q11 q12 q13))).symm).trans (apc2 q14 q15 (((q11 ◇ q13) ◇ q12) ◇ q13) (q11 ◇ q13))).trans (apc0 q11 q12 q13)
  have apc4 : forall (q16 q17 q18 q19:G), ((q18 ◇ q19) ◇ (q16 ◇ q17)) = (q19 ◇ q17):=by
    intro q16 q17 q18 q19
    exact ((congrArg (fun t => (q18 ◇ q19) ◇ t) ((h q16 q17 q19).symm)).symm).trans (apc3 q16 q19 q17 q18 q19)
  have apc5 : forall (x y z:G), (y ◇ z) = (y ◇ x):=by
    intro x y z
    exact ((apc4 (x ◇ y) z z y).symm).trans ((((h x y z).symm).trans (h x y x)).trans (apc4 (x ◇ y) x x y))
  exact (apc5 (x ◇ y) x y).trans ((apc5 (x ◇ y) x (z ◇ ((w ◇ w) ◇ w))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47379_to_42752 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47379_to_42752
