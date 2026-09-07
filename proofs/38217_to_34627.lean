-- Equation38217 → Equation34627
-- Recorded verdict: true
-- Premise: x = ((x * ((y * z) * w)) * w) * u
-- Conclusion: x = ((x * y) * ((y * z) * y)) * y
-- Original submission SHA-256: 92582ad35aa63acdc0d1a11f70044e025eed567c2cf113bd33f1a03473231186
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((x ◇ ((y ◇ z) ◇ w)) ◇ w) ◇ u
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ y) ◇ ((y ◇ z) ◇ y)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (((q3 ◇ q0) ◇ q2) ◇ q1) = q3:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q2) (congrArg (fun t => q3 ◇ t) ((h q0 q0 q0 q0 q2).symm)))).symm).trans ((h q3 (q0 ◇ ((q0 ◇ q0) ◇ q0)) q0 q2 q1).symm)
  exact (calc
    x = x:=rfl
    _ = (((x ◇ y) ◇ ((y ◇ z) ◇ y)) ◇ y):=(apc0 y y ((y ◇ z) ◇ y) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_38217_to_34627 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_38217_to_34627
