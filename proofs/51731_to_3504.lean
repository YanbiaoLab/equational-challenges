-- Equation51731 → Equation3504
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * (z * w)) * u
-- Conclusion: x * x = y * ((z * w) * y)
-- Original submission SHA-256: c91823dcf44374f9d5c849cf37a6a9b8bce3adfa0b894f48b20c6c887805cfcd
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ x) ◇ (z ◇ w)) ◇ u
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ ((z ◇ w) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc1 : forall (q0 q1 q2 q3 q4 q5:G), ((q2 ◇ q0) ◇ q4) = ((q1 ◇ q1) ◇ q3):=by
    intro q0 q1 q2 q3 q4 q5
    exact (((congrArg (fun t => t ◇ q3) (apc0 q1 q5 (q1 ◇ q5) (q1 ◇ q5) (q1 ◇ q5))).symm).trans (((congrArg (fun t => t ◇ q3) ((h q1 q5 q2 q0 ((q2 ◇ q1) ◇ q0)).symm)).symm).trans ((h (q2 ◇ q0) q4 (q2 ◇ q1) q0 q3).symm))).symm
  have apc2 : forall (q6 q7 q8 q9:G), ((q6 ◇ q6) ◇ q7) = (q8 ◇ q8):=by
    intro q6 q7 q8 q9
    exact (((apc1 (q6 ◇ q6) q6 (q6 ◇ q8) q7 q6 q6).symm).trans ((h q8 q9 q6 q6 q6).symm)).trans (apc0 q8 q9 (q8 ◇ q9) (q8 ◇ q9) (q8 ◇ q9))
  have apc5 : forall (q10 q11:G), ((q10 ◇ q10) ◇ (q10 ◇ q10)) = (q11 ◇ q11):=by
    intro q10 q11
    exact (((apc2 q10 q10 q11 q10).symm).trans (apc0 (q10 ◇ q10) q10 q10 q10 q10)).symm
  have apc7 : forall (q12 q13 q14 q15 q16:G), (((q12 ◇ q12) ◇ q13) ◇ ((q12 ◇ q12) ◇ q13)) = (q14 ◇ q14):=by
    intro q12 q13 q14 q15 q16
    exact ((apc0 ((q12 ◇ q12) ◇ q13) ((q15 ◇ q16) ◇ (q15 ◇ q16)) (((q12 ◇ q12) ◇ q13) ◇ ((q15 ◇ q16) ◇ (q15 ◇ q16))) (((q12 ◇ q12) ◇ q13) ◇ ((q15 ◇ q16) ◇ (q15 ◇ q16))) (((q12 ◇ q12) ◇ q13) ◇ ((q15 ◇ q16) ◇ (q15 ◇ q16)))).symm).trans (((congrArg (fun t => t ◇ ((q15 ◇ q16) ◇ (q15 ◇ q16))) (apc1 q16 q12 q15 q13 (q15 ◇ q16) q16)).symm).trans (apc5 (q15 ◇ q16) q14))
  have apc8 : forall (q17 q18 q19:G), (q19 ◇ q19) = (q18 ◇ q17):=by
    intro q17 q18 q19
    exact ((h q18 q17 q18 q17 ((q18 ◇ q18) ◇ (q18 ◇ q17))).trans (apc7 q18 (q18 ◇ q17) q19 q17 q17)).symm
  exact (apc8 (x ◇ x) (x ◇ x) x).trans (apc8 ((z ◇ w) ◇ y) y (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51731_to_3504 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51731_to_3504
