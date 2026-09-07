-- Equation53743 → Equation60409
-- Recorded verdict: true
-- Premise: x * y = (((z * w) * z) * u) * v
-- Conclusion: (x * y) * y = (z * z) * (x * y)
-- Original submission SHA-256: 01d04fa8476c76ac1e0bace3651d62a481284c489327c6288d8641aea0fff7f4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = (((z ◇ w) ◇ z) ◇ u) ◇ v
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ y = (z ◇ z) ◇ (x ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q1) ◇ q2) = (q3 ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ q2) ((h q0 q1 q0 q0 (q0 ◇ q0) q0).symm)).symm).trans ((h q3 q4 (q0 ◇ q0) q0 q0 q2).symm)
  exact (apc0 x y y ((x ◇ y) ◇ y) ((z ◇ z) ◇ (x ◇ y))).trans ((apc0 z z (x ◇ y) ((x ◇ y) ◇ y) ((z ◇ z) ◇ (x ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53743_to_60409 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53743_to_60409
