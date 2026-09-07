-- Equation42337 → Equation57263
-- Recorded verdict: true
-- Premise: x * y = z * (w * (z * (u * x)))
-- Conclusion: x * (y * z) = (w * (w * z)) * y
-- Original submission SHA-256: e3f208fe9071ae2e064776d31012718a9db18ed57bb05ae268ca5ab9961ab324
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (w ◇ (z ◇ (u ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (w ◇ (w ◇ z)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q1 ◇ q0):=by
    intro q0 q1 q2
    exact ((h q1 q0 q0 q0 q0).trans ((h q1 q2 q0 q0 q0).symm)).symm
  have apc1 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc2 : forall (q3 q4 q5 q6:G), (q5 ◇ q3) = (q4 ◇ q4):=by
    intro q3 q4 q5 q6
    exact (((apc0 q3 q5 (q3 ◇ (q5 ◇ (q3 ◇ q4)))).symm).trans ((h q4 q6 q5 q3 q3).symm)).trans (apc1 q4 q6 (q4 ◇ q6) (q4 ◇ q6) (q4 ◇ q6))
  exact (apc2 (y ◇ z) (x ◇ (y ◇ z)) x (x ◇ (y ◇ z))).trans ((apc2 y (x ◇ (y ◇ z)) (w ◇ (w ◇ z)) (x ◇ (y ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42337_to_57263 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42337_to_57263
