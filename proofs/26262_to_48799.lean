-- Equation26262 → Equation48799
-- Recorded verdict: true
-- Premise: x = (y ◇ ((z ◇ x) ◇ x)) ◇ (w ◇ z)
-- Conclusion: x ◇ y = ((x ◇ y) ◇ y) ◇ (y ◇ y)
-- Original submission SHA-256: 8aefc5ffc9574b45d6a5e0a24232b7747ca4e8f9ae7ffcff2e31ca390092fffd
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ ((z ◇ x) ◇ x)) ◇ (w ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = ((x ◇ y) ◇ y) ◇ (y ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3:G), (q0 ◇ (q1 ◇ q3)) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ (q1 ◇ q3)) ((h q0 q0 q2 (q3 ◇ q2)).symm)).symm).trans ((h q2 (q0 ◇ ((q2 ◇ q0) ◇ q0)) q3 q1).symm)
  have apc1 : forall (q0 q2 q1 q3:G), q2 = q0:=by
    intro q0 q2 q1 q3
    exact ((apc0 q0 q1 q2 q3).symm).trans (apc0 q0 q1 q0 q3)
  exact (apc1 (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y)).trans ((apc1 (x ◇ y) (((x ◇ y) ◇ y) ◇ (y ◇ y)) (x ◇ y) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_26262_to_48799 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_26262_to_48799
