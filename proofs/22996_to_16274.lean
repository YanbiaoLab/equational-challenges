-- Equation22996 → Equation16274
-- Recorded verdict: true
-- Premise: x = (y ◇ (z ◇ w)) ◇ ((x ◇ u) ◇ v)
-- Conclusion: x = x ◇ ((((y ◇ z) ◇ w) ◇ x) ◇ y)
-- Original submission SHA-256: 82a0ba3336ae68e7678b63795fd6b077e227b936c3be8b3dda242533f83d2231
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x = (y ◇ (z ◇ w)) ◇ ((x ◇ u) ◇ v)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ ((((y ◇ z) ◇ w) ◇ x) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (q0 ◇ ((q3 ◇ q1) ◇ q2)) = q3:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ ((q3 ◇ q1) ◇ q2)) ((h q0 q0 q0 q0 q0 q0).symm)).symm).trans ((h q3 (q0 ◇ (q0 ◇ q0)) (q0 ◇ q0) q0 q1 q2).symm)
  have apc2 : forall (q4 q5 q6:G), (q5 ◇ q4) = q6:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => q5 ◇ t) (apc0 (q6 ◇ q4) q4 q4 q4)).symm).trans (apc0 q5 q4 ((q4 ◇ q4) ◇ q4) q6)
  exact ((apc2 x ((y ◇ z) ◇ w) x).symm).trans ((apc2 ((((y ◇ z) ◇ w) ◇ x) ◇ y) x (((y ◇ z) ◇ w) ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22996_to_16274 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22996_to_16274
