-- Equation49023 → Equation54871
-- Recorded verdict: true
-- Premise: x * y = ((y * z) * z) * (w * u)
-- Conclusion: x * (x * y) = z * ((w * z) * x)
-- Original submission SHA-256: cc76c95b644ce2ef6272ed466344a9420baf1a04e8d3bcd855907dfb239c70bf
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((y ◇ z) ◇ z) ◇ (w ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = z ◇ ((w ◇ z) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w u
    exact ((h x y z w u).trans ((h y y z w u).symm)).symm
  have apc1 : forall (q0 q1 q2 q3:G), (q0 ◇ ((q3 ◇ q1) ◇ q1)) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((apc0 q0 ((q3 ◇ q1) ◇ q1) q0 q0 q0).symm).trans ((h q2 q3 q1 (q3 ◇ q1) q1).symm)
  have apc3 : forall (q4 q5 q6 q7:G), (q4 ◇ (q5 ◇ q5)) = (q6 ◇ q7):=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => q4 ◇ t) ((apc0 (q7 ◇ q5) q5 q4 q4 q4).symm)).symm).trans (apc1 q4 q5 q6 q7)
  exact ((apc3 (z ◇ ((w ◇ z) ◇ x)) (x ◇ (x ◇ y)) x (x ◇ y)).symm).trans (apc3 (z ◇ ((w ◇ z) ◇ x)) (x ◇ (x ◇ y)) z ((w ◇ z) ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49023_to_54871 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49023_to_54871
