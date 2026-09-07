-- Equation42959 → Equation44336
-- Recorded verdict: true
-- Premise: x * y = z * (x * ((z * w) * z))
-- Conclusion: x * x = y * ((z * (z * w)) * u)
-- Original submission SHA-256: 72ff6701df0d56427dc3d70fe14faf381e5dc0036282b2784aad44f1de67d2cc
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (x ◇ ((z ◇ w) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ x = y ◇ ((z ◇ (z ◇ w)) ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((apc0 q1 (q0 ◇ ((q1 ◇ q0) ◇ q1)) q0 q0).symm).trans ((h q0 q2 q1 q0).symm)).trans (apc0 q0 q2 (q0 ◇ q2) (q0 ◇ q2))
  have apc2 : forall (q3 q4 q5 q6:G), (((q5 ◇ q3) ◇ q5) ◇ q4) = (q5 ◇ q5):=by
    intro q3 q4 q5 q6
    exact (((apc0 q5 (q6 ◇ q6) (q5 ◇ (q6 ◇ q6)) (q5 ◇ (q6 ◇ q6))).symm).trans (((congrArg (fun t => q5 ◇ t) (apc1 q6 ((q5 ◇ q3) ◇ q5) q6)).symm).trans ((h ((q5 ◇ q3) ◇ q5) q4 q5 q3).symm))).symm
  have apc3 : forall (q7 q8 q9 q10:G), ((q8 ◇ q7) ◇ (q8 ◇ q7)) = (q9 ◇ q9):=by
    intro q7 q8 q9 q10
    exact (((congrArg (fun t => (q8 ◇ q7) ◇ t) (apc0 q9 (q8 ◇ q8) (q9 ◇ (q8 ◇ q8)) (q9 ◇ (q8 ◇ q8)))).trans (apc0 (q8 ◇ q7) (q9 ◇ q9) ((q8 ◇ q7) ◇ (q9 ◇ q9)) ((q8 ◇ q7) ◇ (q9 ◇ q9)))).symm).trans ((((congrArg (fun t => (q8 ◇ q7) ◇ t) (congrArg (fun t => q9 ◇ t) (apc2 q7 (q8 ◇ q7) q8 q7))).symm).trans ((h q9 q10 (q8 ◇ q7) q8).symm)).trans (apc0 q9 q10 (q9 ◇ q10) (q9 ◇ q10)))
  have apc4 : forall (q11 q12 q13:G), ((q12 ◇ q12) ◇ (q12 ◇ q11)) = (q13 ◇ q13):=by
    intro q11 q12 q13
    exact ((congrArg (fun t => t ◇ (q12 ◇ q11)) (apc0 q12 q11 q11 q11)).symm).trans (apc3 q11 q12 q13 q11)
  have apc5 : forall (q14 q15 q16:G), (q16 ◇ q16) = (q15 ◇ q14):=by
    intro q14 q15 q16
    exact ((h q15 q14 (q15 ◇ q15) q14).trans (apc4 (((q15 ◇ q15) ◇ q14) ◇ (q15 ◇ q15)) q15 q16)).symm
  exact (apc5 (x ◇ x) (x ◇ x) x).trans (apc5 ((z ◇ (z ◇ w)) ◇ u) y (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42959_to_44336 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42959_to_44336
