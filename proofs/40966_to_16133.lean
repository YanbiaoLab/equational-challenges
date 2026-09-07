-- Equation40966 → Equation16133
-- Recorded verdict: true
-- Premise: x = ((((y * x) * z) * z) * x) * w
-- Conclusion: x = x * ((((x * y) * z) * x) * z)
-- Original submission SHA-256: 027ae501a0a155473ecf8c1004c9247a08783cddecc82b5a63faec06382ec755
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((((y ◇ x) ◇ z) ◇ z) ◇ x) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ ((((x ◇ y) ◇ z) ◇ x) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), (q1 ◇ q0) = q1:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q0) ((h q1 q0 q1 q1).symm)).symm).trans ((h q1 (q0 ◇ q1) q1 q0).symm)
  exact (apc0 ((((x ◇ y) ◇ z) ◇ x) ◇ z) x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_40966_to_16133 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_40966_to_16133
