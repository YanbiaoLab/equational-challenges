-- Equation3768 → Equation43284
-- Recorded verdict: true
-- Premise: x * y = (y * z) * (x * x)
-- Conclusion: x * x = x * ((x * x) * (x * y))
-- Original submission SHA-256: 8897af39ce7d485925494a50a34597f9c356fbed5c1df22ce7caf1c986a9243b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ z) ◇ (x ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = x ◇ ((x ◇ x) ◇ (x ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3:G), ((q0 ◇ q1) ◇ (q3 ◇ q3)) = (q3 ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ (q3 ◇ q3)) ((h q0 q1 q2).symm)).symm).trans ((h q3 (q1 ◇ q2) (q0 ◇ q0)).symm)
  have apc2 : forall (q4 q5 q6 q7:G), (q5 ◇ (q7 ◇ q4)) = (q5 ◇ q6):=by
    intro q4 q5 q6 q7
    exact ((apc0 q6 q7 q4 q5).symm).trans ((h q5 q6 q7).symm)
  exact ((apc2 (x ◇ x) x x x).symm).trans (apc2 (x ◇ x) x ((x ◇ x) ◇ (x ◇ y)) x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3768_to_43284 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3768_to_43284
