-- Equation52589 → Equation41777
-- Recorded verdict: true
-- Premise: x * y = ((z * (x * y)) * w) * z
-- Conclusion: x * y = x * (y * (x * (z * z)))
-- Original submission SHA-256: dd5140d1f252be1d69f502573a82725bf5b4999768aed16bcb8df900a79dc3c3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ (x ◇ y)) ◇ w) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = x ◇ (y ◇ (x ◇ (z ◇ z)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q1) ◇ (q2 ◇ (q0 ◇ q1))) = (q3 ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ (q2 ◇ (q0 ◇ q1))) ((h q0 q1 q2 (q3 ◇ q4)).symm)).symm).trans ((h q3 q4 (q2 ◇ (q0 ◇ q1)) q2).symm)
  have apc1 : forall (q0 q1 q2 q3 q4:G), (q3 ◇ q4) = (q0 ◇ q0):=by
    intro q0 q1 q2 q3 q4
    exact ((apc0 q0 q1 q2 q3 q4).symm).trans (apc0 q0 q1 q2 q0 q0)
  exact (apc1 (x ◇ y) (x ◇ y) (x ◇ y) x y).trans ((apc1 (x ◇ y) (x ◇ y) (x ◇ y) x (y ◇ (x ◇ (z ◇ z)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52589_to_41777 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52589_to_41777
