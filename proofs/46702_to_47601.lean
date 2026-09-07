-- Equation46702 → Equation47601
-- Recorded verdict: true
-- Premise: x * y = (z * w) * (z * (x * x))
-- Conclusion: x * y = (z * w) * ((z * u) * z)
-- Original submission SHA-256: b33dfc242203352cda7142099c214044f5346f54b651c70b87b00d3f7e0fb58d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ w) ◇ (z ◇ (x ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ w) ◇ ((z ◇ u) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y x x).trans ((h x x x x).symm)
  have apc1 : forall (x y z w:G), ((z ◇ w) ◇ (z ◇ w)) = (x ◇ x):=by
    intro x y z w
    exact (((apc0 x x (x ◇ x) (x ◇ x)).symm).trans ((h x x z w).trans ((congrArg (fun t => (z ◇ w) ◇ t) (apc0 z (x ◇ x) (z ◇ (x ◇ x)) (z ◇ (x ◇ x)))).trans (apc0 (z ◇ w) (z ◇ z) ((z ◇ w) ◇ (z ◇ z)) ((z ◇ w) ◇ (z ◇ z)))))).symm
  have apc2 : forall (x y z w:G), (z ◇ z) = (x ◇ x):=by
    intro x y z w
    exact (((apc1 x x z x).symm).trans (apc1 z x z x)).symm
  have apc5 : forall (q0 q1 q2 q3 q4:G), ((q4 ◇ q2) ◇ (q4 ◇ q2)) = ((q1 ◇ q0) ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact (((congrArg (fun t => (q4 ◇ q2) ◇ t) (apc0 q4 (q0 ◇ q0) (q4 ◇ (q0 ◇ q0)) (q4 ◇ (q0 ◇ q0)))).trans (apc0 (q4 ◇ q2) (q4 ◇ q4) ((q4 ◇ q2) ◇ (q4 ◇ q4)) ((q4 ◇ q2) ◇ (q4 ◇ q4)))).symm).trans (((congrArg (fun t => (q4 ◇ q2) ◇ t) (congrArg (fun t => q4 ◇ t) (apc1 q0 q0 q1 q0))).symm).trans ((h (q1 ◇ q0) q3 q4 q2).symm))
  have apc6 : forall (q5 q6 q7 q8:G), ((q6 ◇ q5) ◇ q7) = (q8 ◇ q8):=by
    intro q5 q6 q7 q8
    exact ((apc5 q5 q6 q5 q7 q5).symm).trans (apc2 q8 q5 (q5 ◇ q5) q5)
  have apc86 : forall (q9 q10 q11 q12 q13:G), (((q10 ◇ q9) ◇ q12) ◇ (q11 ◇ q11)) = (q13 ◇ q13):=by
    intro q9 q10 q11 q12 q13
    exact ((congrArg (fun t => ((q10 ◇ q9) ◇ q12) ◇ t) (apc6 q9 q10 q12 q11)).symm).trans (apc1 q13 q9 (q10 ◇ q9) q12)
  have apc87 : forall (q14 q15 q16:G), (q16 ◇ q16) = (q15 ◇ q14):=by
    intro q14 q15 q16
    exact ((h q15 q14 (q15 ◇ q15) q14).trans (apc86 q15 q15 (q15 ◇ q15) q14 q16)).symm
  exact ((apc87 y x (x ◇ y)).symm).trans (apc87 ((z ◇ u) ◇ z) (z ◇ w) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46702_to_47601 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46702_to_47601
