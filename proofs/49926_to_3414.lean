-- Equation49926 → Equation3414
-- Recorded verdict: true
-- Premise: x * y = (y * (z * (w * u))) * v
-- Conclusion: x * y = z * (z * (x * y))
-- Original submission SHA-256: b6460c8cddd1669418b76bc45962d6e0d877a0c4b60f71d81609b24128d5cc61
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = (y ◇ (z ◇ (w ◇ u))) ◇ v
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ (z ◇ (x ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w u v:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w u v
    exact ((h x y z w u v).trans ((h y y z w u v).symm)).symm
  have apc2 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact ((apc0 (q2 ◇ (q0 ◇ (q0 ◇ q0))) q0 q0 q0 q0 q0).trans ((h q1 q2 q0 q0 q0 q0).symm)).symm
  exact (apc2 (x ◇ y) x y).trans ((apc2 (x ◇ y) z (z ◇ (x ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49926_to_3414 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49926_to_3414
