-- Equation37691 → Equation52111
-- Recorded verdict: true
-- Premise: x = ((y * (z * (x * z))) * z) * x
-- Conclusion: x * x = ((y * (x * x)) * z) * x
-- Original submission SHA-256: 7e2a689d1969bacc08e090e566aa8b1580cbd343668f046baa21fe90673bdc8a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ (z ◇ (x ◇ z))) ◇ z) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ (x ◇ x)) ◇ z) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc1 : forall (q0 q1:G), (q1 ◇ q0) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q0) ((h q1 q0 (q1 ◇ (q0 ◇ q1))).symm)).symm).trans ((h q0 (q0 ◇ ((q1 ◇ (q0 ◇ q1)) ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1))))) q1).symm)
  exact (apc1 x x).trans ((apc1 x ((y ◇ (x ◇ x)) ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_37691_to_52111 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_37691_to_52111
