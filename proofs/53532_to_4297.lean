-- Equation53532 → Equation4297
-- Recorded verdict: true
-- Premise: x * y = (((z * y) * y) * x) * w
-- Conclusion: x * (x * y) = y * (z * z)
-- Original submission SHA-256: 8dc5dc4b10e40b4209761a336caac80039668fc2555657d33fe7c11649c1baa9
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (((z ◇ y) ◇ y) ◇ x) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ y) = y ◇ (z ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ q0) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q0) ((h q2 q2 q0 q1).symm)).symm).trans ((h q1 q2 (q0 ◇ q2) q0).symm)
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((apc0 q0 q1 q2).symm).trans (apc0 q0 q0 q2)
  have apc2 : forall (q3 q4 q5 q6:G), (q5 ◇ q6) = (q3 ◇ q4):=by
    intro q3 q4 q5 q6
    exact (((apc1 q3 (q6 ◇ q6) q4).symm).trans (apc0 q4 q5 q6)).symm
  exact (apc2 (x ◇ (x ◇ y)) (y ◇ (z ◇ z)) x (x ◇ y)).trans ((apc2 (x ◇ (x ◇ y)) (y ◇ (z ◇ z)) y (z ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53532_to_4297 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53532_to_4297
