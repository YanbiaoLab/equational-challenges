-- Equation52904 → Equation47606
-- Recorded verdict: true
-- Premise: x * y = ((z * (w * u)) * y) * v
-- Conclusion: x * y = (z * w) * ((w * x) * y)
-- Original submission SHA-256: c225ede4e45a3941b49059ab402f295c44600cd89048302b1e01652719489eb4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = ((z ◇ (w ◇ u)) ◇ y) ◇ v
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ w) ◇ ((w ◇ x) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u v:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w u v
    exact ((h x y z w u v).trans ((h y y z w u v).symm)).symm
  have apc1 : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ q0) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q0) ((apc0 (q0 ◇ (q0 ◇ q0)) q2 q0 q0 q0 q0).symm)).symm).trans ((h q1 q2 q0 q0 q0 q0).symm)
  have apc4 : forall (q3 q4 q5 q6:G), ((q6 ◇ q6) ◇ q5) = (q3 ◇ q4):=by
    intro q3 q4 q5 q6
    exact (((apc1 q6 q3 q4).symm).trans ((apc1 q5 (q4 ◇ q4) q6).symm)).symm
  exact ((apc4 x y ((z ◇ w) ◇ ((w ◇ x) ◇ y)) (x ◇ y)).symm).trans (apc4 (z ◇ w) ((w ◇ x) ◇ y) ((z ◇ w) ◇ ((w ◇ x) ◇ y)) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52904_to_47606 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52904_to_47606
