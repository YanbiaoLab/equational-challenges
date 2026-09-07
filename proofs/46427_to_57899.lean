-- Equation46427 → Equation57899
-- Recorded verdict: true
-- Premise: x * y = (z * x) * (x * (z * x))
-- Conclusion: x * (y * z) = ((y * x) * x) * z
-- Original submission SHA-256: a9e9fb5ef92c4a24b5791e56d2cb4b8c9200f8c91a3ac0b12693f2a9cf9a311d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ x) ◇ (x ◇ (z ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = ((y ◇ x) ◇ x) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q1 ◇ q1) ◇ t) (apc0 q0 (q1 ◇ q0) (q0 ◇ (q1 ◇ q0)))).symm).trans ((((congrArg (fun t => t ◇ (q0 ◇ (q1 ◇ q0))) (apc0 q1 q0 q0)).symm).trans ((h q0 q2 q1).symm)).trans (apc0 q0 q2 (q0 ◇ q2)))
  have apc2 : forall (q3 q4 q5:G), ((q3 ◇ q3) ◇ q4) = (q3 ◇ q3):=by
    intro q3 q4 q5
    exact (((((congrArg (fun t => (q3 ◇ q3) ◇ t) (congrArg (fun t => (q3 ◇ q3) ◇ t) (apc1 q3 q5 ((q5 ◇ q5) ◇ (q3 ◇ q3))))).trans (congrArg (fun t => (q3 ◇ q3) ◇ t) (apc1 q3 q3 ((q3 ◇ q3) ◇ (q3 ◇ q3))))).trans (apc1 q3 q3 ((q3 ◇ q3) ◇ (q3 ◇ q3)))).symm).trans (((congrArg (fun t => t ◇ ((q3 ◇ q3) ◇ ((q5 ◇ q5) ◇ (q3 ◇ q3)))) (apc1 q3 q5 q3)).symm).trans ((h (q3 ◇ q3) q4 (q5 ◇ q5)).symm))).symm
  have apc4 : forall (x y z:G), ((z ◇ x) ◇ (x ◇ x)) = (x ◇ x):=by
    intro x y z
    exact ((congrArg (fun t => (z ◇ x) ◇ t) (apc0 x (z ◇ x) (x ◇ (z ◇ x)))).symm).trans ((((h x y z).symm).trans (h x y x)).trans ((congrArg (fun t => (x ◇ x) ◇ t) (apc0 x (x ◇ x) (x ◇ (x ◇ x)))).trans (apc2 x (x ◇ x) ((x ◇ x) ◇ (x ◇ x)))))
  have apc5 : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ (q1 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((apc0 (q1 ◇ q0) (q0 ◇ (q1 ◇ q0)) q0).symm).trans ((h q0 q2 q1).symm)).trans (apc0 q0 q2 (q0 ◇ q2))
  have apc6 : forall (q6 q7 q8:G), ((q7 ◇ q6) ◇ q8) = (q6 ◇ q6):=by
    intro q6 q7 q8
    exact (((((congrArg (fun t => (q6 ◇ q6) ◇ t) (congrArg (fun t => (q7 ◇ q6) ◇ t) (apc5 q6 q7 ((q7 ◇ q6) ◇ (q7 ◇ q6))))).trans (congrArg (fun t => (q6 ◇ q6) ◇ t) (apc4 q6 ((q7 ◇ q6) ◇ (q6 ◇ q6)) q7))).trans (apc2 q6 (q6 ◇ q6) ((q6 ◇ q6) ◇ (q6 ◇ q6)))).symm).trans (((congrArg (fun t => t ◇ ((q7 ◇ q6) ◇ ((q7 ◇ q6) ◇ (q7 ◇ q6)))) (apc5 q6 q7 q6)).symm).trans ((h (q7 ◇ q6) q8 (q7 ◇ q6)).symm))).symm
  exact (calc
    (x ◇ (y ◇ z)) = (x ◇ x):=(congrArg (fun t => x ◇ t) (apc0 y z (y ◇ z))).trans (apc0 x (y ◇ y) (x ◇ (y ◇ y)))
    _ = (((y ◇ x) ◇ x) ◇ z):=((congrArg (fun t => t ◇ z) (apc6 x y x)).trans (apc6 x x z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46427_to_57899 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46427_to_57899
