-- Equation42975 → Equation4077
-- Recorded verdict: true
-- Premise: x * y = z * (x * ((w * z) * w))
-- Conclusion: x * x = ((x * y) * z) * y
-- Original submission SHA-256: 527a2138b92fb13f02e3a602ef394f56079fabfd618e6705b9ab9fad8c72328c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (x ◇ ((w ◇ z) ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = ((x ◇ y) ◇ z) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y x x).trans ((h x x x x).symm)
  have apc1 : forall (x y z w:G), (z ◇ z) = (x ◇ x):=by
    intro x y z w
    exact (((apc0 x x (x ◇ x) (x ◇ x)).symm).trans ((h x x z x).trans (((congrArg (fun t => z ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ x) (apc0 x z (x ◇ z) (x ◇ z))))).trans (congrArg (fun t => z ◇ t) (apc0 x ((x ◇ x) ◇ x) (x ◇ ((x ◇ x) ◇ x)) (x ◇ ((x ◇ x) ◇ x))))).trans (apc0 z (x ◇ x) (z ◇ (x ◇ x)) (z ◇ (x ◇ x)))))).symm
  have apc2 : forall (q0 q1 q2:G), (((q0 ◇ q0) ◇ q0) ◇ q1) = (q2 ◇ q2):=by
    intro q0 q1 q2
    exact (((apc0 q2 (q0 ◇ q0) (q2 ◇ (q0 ◇ q0)) (q2 ◇ (q0 ◇ q0))).symm).trans ((((congrArg (fun t => q2 ◇ t) (apc1 q0 q0 ((q0 ◇ q2) ◇ q0) q0)).symm).trans ((h ((q0 ◇ q2) ◇ q0) q1 q2 q0).symm)).trans (congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q0) (apc0 q0 q2 (q0 ◇ q2) (q0 ◇ q2)))))).symm
  have apc81 : forall (q3 q4:G), (((q3 ◇ q3) ◇ q3) ◇ ((q3 ◇ q3) ◇ q3)) = (q4 ◇ q4):=by
    intro q3 q4
    exact (((apc2 q3 q3 q4).symm).trans (apc0 ((q3 ◇ q3) ◇ q3) q3 q3 q3)).symm
  have apc82 : forall (q5 q6:G), (((q6 ◇ q6) ◇ q6) ◇ q5) = (q6 ◇ q6):=by
    intro q5 q6
    exact (((apc0 q6 (q5 ◇ q5) (q6 ◇ (q5 ◇ q5)) (q6 ◇ (q5 ◇ q5))).symm).trans (((congrArg (fun t => q6 ◇ t) (apc81 q6 q5)).symm).trans ((h ((q6 ◇ q6) ◇ q6) q5 q6 q6).symm))).symm
  have apc83 : forall (q7 q8 q9:G), (((q7 ◇ q7) ◇ q9) ◇ q8) = (q9 ◇ q9):=by
    intro q7 q8 q9
    exact ((congrArg (fun t => t ◇ q8) (congrArg (fun t => t ◇ q9) (apc1 q7 q7 q9 q7))).symm).trans (apc82 q8 q9)
  have apc84 : forall (q10:G), ((q10 ◇ q10) ◇ (q10 ◇ q10)) = (q10 ◇ q10):=by
    intro q10
    exact ((apc83 q10 q10 (q10 ◇ q10)).symm).trans (((congrArg (fun t => t ◇ q10) (apc0 (q10 ◇ q10) q10 q10 q10)).symm).trans (apc82 q10 q10))
  have apc85 : forall (q11 q12:G), ((q11 ◇ q11) ◇ q12) = (q11 ◇ q11):=by
    intro q11 q12
    exact (((congrArg (fun t => t ◇ q12) (apc84 q11)).symm).trans (apc83 q11 q12 (q11 ◇ q11))).trans (apc84 q11)
  exact (calc
    (x ◇ x) = (x ◇ x):=rfl
    _ = (((x ◇ y) ◇ z) ◇ y):=(((congrArg (fun t => t ◇ y) (congrArg (fun t => t ◇ z) (apc0 x y (x ◇ y) (x ◇ y)))).trans (congrArg (fun t => t ◇ y) (apc85 x z))).trans (apc85 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42975_to_4077 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42975_to_4077
