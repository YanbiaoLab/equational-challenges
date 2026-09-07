-- Equation49366 → Equation57811
-- Recorded verdict: true
-- Premise: x * y = ((z * w) * w) * (y * z)
-- Conclusion: x * (y * y) = ((z * w) * w) * z
-- Original submission SHA-256: 9a236c9efe17d30e844126815abf0b49f701dee3705474fd2f5f937462fc2d90
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ w) ◇ w) ◇ (y ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = ((z ◇ w) ◇ w) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc3 : forall (q0 q1 q2 q3:G), (((q3 ◇ q0) ◇ q0) ◇ (q3 ◇ q3)) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => ((q3 ◇ q0) ◇ q0) ◇ t) ((apc0 q2 q3 q0 q0).symm)).symm).trans ((h q1 q2 q3 q0).symm)
  exact ((apc3 (((z ◇ w) ◇ w) ◇ z) x (y ◇ y) (x ◇ (y ◇ y))).symm).trans (apc3 (((z ◇ w) ◇ w) ◇ z) ((z ◇ w) ◇ w) z (x ◇ (y ◇ y)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49366_to_57811 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49366_to_57811
