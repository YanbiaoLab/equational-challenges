-- Equation43254 → Equation51429
-- Recorded verdict: true
-- Premise: x * y = z * (w * ((u * y) * z))
-- Conclusion: x * y = ((x * y) * (y * y)) * x
-- Original submission SHA-256: 8f3a56f6d733c162e3d1b619a57f25050ea4a137955fcb7b674e9c827c3cf035
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (w ◇ ((u ◇ y) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = ((x ◇ y) ◇ (y ◇ y)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc2 : forall (q0 q1 q2 q3 q4 q5:G), (((q0 ◇ q2) ◇ q3) ◇ (q1 ◇ q2)) = (q4 ◇ q5):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => ((q0 ◇ q2) ◇ q3) ◇ t) ((h q1 q2 q3 (q0 ◇ q5) q0).symm)).symm).trans ((h q4 q5 ((q0 ◇ q2) ◇ q3) q3 q0).symm)
  have apc3 : forall (q0 q1 q2 q3 q4 q5:G), (q4 ◇ q5) = (q0 ◇ q0):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((apc2 q0 q1 q2 q3 q4 q5).symm).trans (apc2 q0 q1 q2 q3 q0 q0)
  exact (apc3 (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y) x y).trans ((apc3 (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y) ((x ◇ y) ◇ (y ◇ y)) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43254_to_51429 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43254_to_51429
