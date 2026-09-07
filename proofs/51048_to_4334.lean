-- Equation51048 → Equation4334
-- Recorded verdict: true
-- Premise: x * y = (z * ((w * x) * z)) * w
-- Conclusion: x * (y * x) = z * (w * x)
-- Original submission SHA-256: 3aeeb9e4d629605536ce8e52a135cea63f32815ae30dc5cbf8e980e86bf7a456
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ ((w ◇ x) ◇ z)) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ x) = z ◇ (w ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc4 : forall (x y z w:G), ((z ◇ z) ◇ w) = ((x ◇ x) ◇ x):=by
    intro x y z w
    exact (((congrArg (fun t => t ◇ w) (congrArg (fun t => z ◇ t) (congrArg (fun t => t ◇ z) (apc0 w x (w ◇ x) (w ◇ x))))).trans (congrArg (fun t => t ◇ w) (apc0 z ((w ◇ w) ◇ z) (z ◇ ((w ◇ w) ◇ z)) (z ◇ ((w ◇ w) ◇ z))))).symm).trans ((((h x y z w).symm).trans (h x y x x)).trans (congrArg (fun t => t ◇ x) (apc0 x ((x ◇ x) ◇ x) (x ◇ ((x ◇ x) ◇ x)) (x ◇ ((x ◇ x) ◇ x)))))
  have apc14 : forall (q0 q1 q2 q3 q4 q5:G), ((q2 ◇ q2) ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2 q3 q4 q5
    exact (((apc0 q0 q3 (q0 ◇ q3) (q0 ◇ q3)).symm).trans (((h q0 q3 q4 q5).trans (h (q4 ◇ ((q5 ◇ q0) ◇ q4)) q5 q2 q1)).trans (((congrArg (fun t => t ◇ q1) (congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ q2) (congrArg (fun t => q1 ◇ t) (apc0 q4 ((q5 ◇ q0) ◇ q4) (q4 ◇ ((q5 ◇ q0) ◇ q4)) (q4 ◇ ((q5 ◇ q0) ◇ q4))))))).trans (congrArg (fun t => t ◇ q1) (congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ q2) (apc0 q1 (q4 ◇ q4) (q1 ◇ (q4 ◇ q4)) (q1 ◇ (q4 ◇ q4))))))).trans (congrArg (fun t => t ◇ q1) (apc0 q2 ((q1 ◇ q1) ◇ q2) (q2 ◇ ((q1 ◇ q1) ◇ q2)) (q2 ◇ ((q1 ◇ q1) ◇ q2))))))).symm
  have apc15 : forall (q6 q7 q8 q9:G), ((q7 ◇ q7) ◇ q7) = (q7 ◇ q6):=by
    intro q6 q7 q8 q9
    exact ((congrArg (fun t => t ◇ q7) (apc0 q7 ((q8 ◇ q8) ◇ q9) (q7 ◇ ((q8 ◇ q8) ◇ q9)) (q7 ◇ ((q8 ◇ q8) ◇ q9)))).symm).trans (((congrArg (fun t => t ◇ q7) (congrArg (fun t => q7 ◇ t) ((apc4 q7 q9 q8 q9).symm))).symm).trans ((h q7 q6 q7 q7).symm))
  have apc16 : forall (q10 q11 q12:G), (q12 ◇ q10) = (q11 ◇ q11):=by
    intro q10 q11 q12
    exact ((apc15 q10 q12 q10 q10).symm).trans (apc14 q11 q12 q12 q10 q10 q10)
  exact (apc16 (y ◇ x) (x ◇ (y ◇ x)) x).trans ((apc16 (w ◇ x) (x ◇ (y ◇ x)) z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51048_to_4334 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51048_to_4334
