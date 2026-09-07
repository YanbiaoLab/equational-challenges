-- Equation51755 → Equation57877
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * (w * u)) * w
-- Conclusion: x * (y * z) = ((x * w) * y) * y
-- Original submission SHA-256: ab975cf81fa9d79b2239d5d75feb55482807b7133ecea16756bb44cc33a9600d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ x) ◇ (w ◇ u)) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = ((x ◇ w) ◇ y) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc1 : forall (q0 q1 q2 q3:G), (((q2 ◇ q1) ◇ (q2 ◇ q1)) ◇ q0) = (q1 ◇ q1):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => t ◇ q0) (apc0 (q2 ◇ q1) (q0 ◇ q0) q0 q0 q0)).symm).trans ((h q1 q3 q2 q0 q0).symm)).trans (apc0 q1 q3 (q1 ◇ q3) (q1 ◇ q3) (q1 ◇ q3))
  have apc2 : forall (q0 q1 q2 q3:G), (((q2 ◇ q1) ◇ (q0 ◇ q0)) ◇ q0) = (q1 ◇ q1):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => t ◇ q0) (congrArg (fun t => (q2 ◇ q1) ◇ t) (apc0 q0 q0 q0 q0 q0))).symm).trans ((h q1 q3 q2 q0 q0).symm)).trans (apc0 q1 q3 (q1 ◇ q3) (q1 ◇ q3) (q1 ◇ q3))
  have apc7 : forall (q4 q5:G), ((q4 ◇ q4) ◇ q5) = (q5 ◇ q5):=by
    intro q4 q5
    exact (((congrArg (fun t => t ◇ q5) (apc2 (q5 ◇ q5) q4 q4 q4)).symm).trans (apc2 q5 ((q5 ◇ q5) ◇ (q5 ◇ q5)) (q4 ◇ q4) q4)).trans (apc1 ((q5 ◇ q5) ◇ (q5 ◇ q5)) q5 q5 (((q5 ◇ q5) ◇ (q5 ◇ q5)) ◇ ((q5 ◇ q5) ◇ (q5 ◇ q5))))
  have apc8 : forall (q6 q7 q8 q9 q10 q11:G), (((q8 ◇ q7) ◇ q6) ◇ q9) = (q8 ◇ q8):=by
    intro q6 q7 q8 q9 q10 q11
    exact ((((congrArg (fun t => t ◇ q8) (apc0 q10 q11 (q10 ◇ q11) (q10 ◇ q11) (q10 ◇ q11))).trans (apc7 q10 q8)).symm).trans (((congrArg (fun t => t ◇ q8) ((h q10 q11 q6 (q8 ◇ q7) q6).symm)).symm).trans ((h ((q8 ◇ q7) ◇ q6) q9 (q6 ◇ q10) q8 q7).symm))).symm
  exact (calc
    (x ◇ (y ◇ z)) = (x ◇ x):=(congrArg (fun t => x ◇ t) (apc0 y z (y ◇ z) (y ◇ z) (y ◇ z))).trans (apc0 x (y ◇ y) (x ◇ (y ◇ y)) (x ◇ (y ◇ y)) (x ◇ (y ◇ y)))
    _ = (((x ◇ w) ◇ y) ◇ y):=(apc8 y w x y (((x ◇ w) ◇ y) ◇ y) (((x ◇ w) ◇ y) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51755_to_57877 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51755_to_57877
