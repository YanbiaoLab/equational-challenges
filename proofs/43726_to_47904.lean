-- Equation43726 → Equation47904
-- Recorded verdict: true
-- Premise: x * y = y * ((z * x) * (w * w))
-- Conclusion: x * y = (x * (x * z)) * (w * y)
-- Original submission SHA-256: 7b6a71e173d2c16c57904fd279bcaada25d0faa0331fbb5dda6e22bec78fddee
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ ((z ◇ x) ◇ (w ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (x ◇ (x ◇ z)) ◇ (w ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ (q0 ◇ (q3 ◇ q1))) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) ((h q0 (q3 ◇ q1) q0 q0).symm)).symm).trans ((h q1 q2 q3 (q0 ◇ q0)).symm)
  have apc1 : forall (q4 q5 q6:G), (q5 ◇ q6) = (q4 ◇ q6):=by
    intro q4 q5 q6
    exact (((apc0 (q4 ◇ q5) q4 q6 q4).symm).trans ((h q5 q6 q4 q4).symm)).symm
  have apc3 : forall (q7 q8 q9 q10 q11:G), (q9 ◇ q10) = (q8 ◇ q7):=by
    intro q7 q8 q9 q10 q11
    exact (((apc0 (q11 ◇ q9) q8 q7 q8).symm).trans (((apc1 q7 q10 ((q11 ◇ q9) ◇ (q8 ◇ q8))).symm).trans ((h q9 q10 q11 q8).symm))).symm
  exact (apc3 (x ◇ y) ((x ◇ (x ◇ z)) ◇ (w ◇ y)) x y (x ◇ y)).trans ((apc3 (x ◇ y) ((x ◇ (x ◇ z)) ◇ (w ◇ y)) (x ◇ (x ◇ z)) (w ◇ y) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43726_to_47904 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43726_to_47904
