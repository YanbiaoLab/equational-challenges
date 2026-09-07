-- Equation51869 → Equation53089
-- Recorded verdict: true
-- Premise: x * y = ((z * z) * (z * x)) * x
-- Conclusion: x * x = (((y * z) * y) * w) * u
-- Original submission SHA-256: adb41b6ac5c0052d8c6df350b522d189d144bad1a9539bfa041d556acce9da76
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ z) ◇ (z ◇ x)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ x = (((y ◇ z) ◇ y) ◇ w) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc1 : forall (q0 q1 q2:G), (((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ q0) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => t ◇ q0) (apc0 (q1 ◇ q1) (q1 ◇ q0) q0)).symm).trans ((h q0 q2 q1).symm)).trans (apc0 q0 q2 (q0 ◇ q2))
  have apc3 : forall (q3 q4 q5:G), ((((q3 ◇ q3) ◇ q4) ◇ ((q3 ◇ q3) ◇ q4)) ◇ q4) = (q4 ◇ q4):=by
    intro q3 q4 q5
    exact (((congrArg (fun t => t ◇ q4) (apc1 ((q3 ◇ q3) ◇ q4) q3 q3)).symm).trans ((h q4 q5 (q3 ◇ q3)).symm)).trans (apc0 q4 q5 (q4 ◇ q5))
  have apc6 : forall (q6 q7:G), ((q6 ◇ q6) ◇ (q6 ◇ q6)) = ((q6 ◇ q6) ◇ q7):=by
    intro q6 q7
    exact ((apc3 q6 (q6 ◇ q6) q6).symm).trans ((h (q6 ◇ q6) q7 (q6 ◇ q6)).symm)
  have apc8 : forall (q8 q9 q10:G), (((q10 ◇ q10) ◇ q8) ◇ q9) = (q9 ◇ q9):=by
    intro q8 q9 q10
    exact ((congrArg (fun t => t ◇ q9) (apc6 q10 q8)).symm).trans (apc1 q9 q10 q8)
  have apc10 : forall (q11 q12 q13:G), ((q12 ◇ q11) ◇ q13) = (q13 ◇ q13):=by
    intro q11 q12 q13
    exact ((congrArg (fun t => t ◇ q13) ((h q12 q11 q12).symm)).symm).trans (apc8 q12 q13 (q12 ◇ q12))
  have apc11 : forall (q14 q15 q16 q17:G), (((q15 ◇ q15) ◇ (q15 ◇ q15)) ◇ ((q15 ◇ q15) ◇ (q15 ◇ q15))) = (q16 ◇ q14):=by
    intro q14 q15 q16 q17
    exact (((h q16 q14 q15).trans (h ((q15 ◇ q15) ◇ (q15 ◇ q16)) q16 q17)).trans ((((congrArg (fun t => t ◇ ((q15 ◇ q15) ◇ (q15 ◇ q16))) (congrArg (fun t => (q17 ◇ q17) ◇ t) (congrArg (fun t => q17 ◇ t) (congrArg (fun t => (q15 ◇ q15) ◇ t) (apc0 q15 q16 (q15 ◇ q16)))))).trans (congrArg (fun t => ((q17 ◇ q17) ◇ (q17 ◇ ((q15 ◇ q15) ◇ (q15 ◇ q15)))) ◇ t) (congrArg (fun t => (q15 ◇ q15) ◇ t) (apc0 q15 q16 (q15 ◇ q16))))).trans (congrArg (fun t => t ◇ ((q15 ◇ q15) ◇ (q15 ◇ q15))) (congrArg (fun t => (q17 ◇ q17) ◇ t) (apc0 q17 ((q15 ◇ q15) ◇ (q15 ◇ q15)) (q17 ◇ ((q15 ◇ q15) ◇ (q15 ◇ q15))))))).trans (apc10 (q17 ◇ q17) (q17 ◇ q17) ((q15 ◇ q15) ◇ (q15 ◇ q15))))).symm
  exact ((apc11 x (x ◇ x) x (x ◇ x)).symm).trans (apc11 u (x ◇ x) (((y ◇ z) ◇ y) ◇ w) (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51869_to_53089 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51869_to_53089
