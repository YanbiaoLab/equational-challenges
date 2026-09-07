-- Equation36495 → Equation27493
-- Recorded verdict: true
-- Premise: x = (((y * x) * x) * (z * y)) * y
-- Conclusion: x = ((y * z) * (w * u)) * (v * w)
-- Original submission SHA-256: 56ba86c1dab83563afe6e3cbbdab9c99fe844fa51279244781b9de0bf2e34b29
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((y ◇ x) ◇ x) ◇ (z ◇ y)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x = ((y ◇ z) ◇ (w ◇ u)) ◇ (v ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have apc0 : forall (q0 q1 q2:G), ((((q2 ◇ q1) ◇ q1) ◇ q0) ◇ q2) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q2) (congrArg (fun t => ((q2 ◇ q1) ◇ q1) ◇ t) ((h q0 q2 q0).symm))).symm).trans ((h q1 q2 (((q2 ◇ q0) ◇ q0) ◇ (q0 ◇ q2))).symm)
  have apc1 : forall (q3 q4:G), (q4 ◇ (q3 ◇ q4)) = q4:=by
    intro q3 q4
    exact ((congrArg (fun t => t ◇ (q3 ◇ q4)) (apc0 q4 q4 q3)).symm).trans (apc0 q3 q4 (q3 ◇ q4))
  have apc2 : forall (q5 q6:G), (((q6 ◇ q5) ◇ q5) ◇ q6) = q5:=by
    intro q5 q6
    exact ((congrArg (fun t => t ◇ q6) (apc1 q5 ((q6 ◇ q5) ◇ q5))).symm).trans (apc0 (q5 ◇ ((q6 ◇ q5) ◇ q5)) q5 q6)
  have apc5 : forall (q7 q8:G), (q8 ◇ q7) = q8:=by
    intro q7 q8
    exact ((congrArg (fun t => q8 ◇ t) ((h q7 q8 q7).symm)).symm).trans (apc1 (((q8 ◇ q7) ◇ q7) ◇ (q7 ◇ q8)) q8)
  have apc6 : forall (q9 q10:G), q10 = q9:=by
    intro q9 q10
    exact (((((congrArg (fun t => q9 ◇ t) (congrArg (fun t => t ◇ q9) (apc5 q9 q10))).trans (congrArg (fun t => q9 ◇ t) (apc5 q9 q10))).trans (apc5 q10 q9)).symm).trans (((congrArg (fun t => t ◇ ((q10 ◇ q9) ◇ q9)) (apc0 q10 q9 q10)).symm).trans (apc2 q10 ((q10 ◇ q9) ◇ q9)))).symm
  exact (apc6 x x).trans ((apc6 x (((y ◇ z) ◇ (w ◇ u)) ◇ (v ◇ w))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_36495_to_27493 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_36495_to_27493
