-- Equation47482 → Equation51503
-- Recorded verdict: true
-- Premise: x * y = (z * z) * ((y * w) * w)
-- Conclusion: x * y = ((x * z) * (z * w)) * u
-- Original submission SHA-256: 60d83460a8db74b5fed113bc763ed6fded9ed2d4b9f7baf80b172b235f6e1230
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ z) ◇ ((y ◇ w) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((x ◇ z) ◇ (z ◇ w)) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc2 : forall (q0 q1 q2:G), (((q2 ◇ q0) ◇ q0) ◇ ((q2 ◇ q0) ◇ q0)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact (apc0 (q0 ◇ q0) ((q2 ◇ q0) ◇ q0) q0 q0).trans ((h q1 q2 q0 q0).symm)
  have apc3 : forall (q3 q4 q5:G), (((q5 ◇ q3) ◇ q3) ◇ (q3 ◇ q3)) = (q4 ◇ q5):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => ((q5 ◇ q3) ◇ q3) ◇ t) ((apc0 (q5 ◇ q3) q3 q3 q3).symm)).symm).trans (apc2 q3 q4 q5)
  have apc6 : forall (q6 q7 q8:G), (((q6 ◇ q7) ◇ q7) ◇ (q7 ◇ q7)) = (q8 ◇ q7):=by
    intro q6 q7 q8
    exact ((congrArg (fun t => t ◇ (q7 ◇ q7)) (congrArg (fun t => t ◇ q7) (apc0 q6 q7 q6 q6))).symm).trans (apc3 q7 q8 q7)
  have apc7 : forall (q9 q10 q11 q12:G), (q11 ◇ q12) = (q9 ◇ q10):=by
    intro q9 q10 q11 q12
    exact (((apc6 q12 q10 q9).symm).trans (apc3 q10 q11 q12)).symm
  have apc8 : forall (q9 q10 q11 q12:G), (q11 ◇ q11) = (q9 ◇ q10):=by
    intro q9 q10 q11 q12
    exact (((apc7 q9 q10 q11 q12).symm).trans (apc7 q11 q11 q11 q12)).symm
  exact ((apc8 x y (x ◇ y) (x ◇ y)).symm).trans (apc8 ((x ◇ z) ◇ (z ◇ w)) u (x ◇ y) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47482_to_51503 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47482_to_51503
