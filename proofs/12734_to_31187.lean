-- Equation12734 → Equation31187
-- Recorded verdict: true
-- Premise: x = x * ((y * (z * (y * x))) * w)
-- Conclusion: x = (x * ((y * z) * (w * y))) * x
-- Original submission SHA-256: 1aae167b43f579b9363645253842a17a59ba2d1a3cf644dca4c51ee77d16403f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ ((y ◇ (z ◇ (y ◇ x))) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ ((y ◇ z) ◇ (w ◇ y))) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ (q2 ◇ q0)) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q1 ◇ t) (congrArg (fun t => t ◇ q0) ((h q2 q0 q0 (q2 ◇ q1)).symm))).symm).trans ((h q1 q2 (q0 ◇ (q0 ◇ (q0 ◇ q2))) q0).symm)
  have apc1 : forall (q3 q4:G), (q3 ◇ q4) = q3:=by
    intro q3 q4
    exact ((congrArg (fun t => q3 ◇ t) (apc0 q3 q4 q3)).symm).trans (apc0 (q3 ◇ q3) q3 q4)
  exact ((apc1 x ((y ◇ z) ◇ (w ◇ y))).symm).trans ((apc1 (x ◇ ((y ◇ z) ◇ (w ◇ y))) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_12734_to_31187 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_12734_to_31187
