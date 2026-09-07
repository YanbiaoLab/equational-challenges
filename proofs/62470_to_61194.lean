-- Equation62470 → Equation61194
-- Recorded verdict: true
-- Premise: (x * y) * z = ((w * y) * y) * w
-- Conclusion: (x * y) * y = (x * (y * z)) * y
-- Original submission SHA-256: 6265724c7dd15cde6b0d128c8f603de59ac4e6e6ad4e23fb5c311670a60f47e5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = ((w ◇ y) ◇ y) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ y = (x ◇ (y ◇ z)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), ((y ◇ y) ◇ y) = ((x ◇ y) ◇ z):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y y w).symm)).symm
  have apc6 : forall (q0 q1 q2 q3 q4:G), (((q0 ◇ q3) ◇ q1) ◇ q3) = ((q2 ◇ q3) ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ q3) (apc0 q0 q3 q1 q0)).symm).trans ((h q2 q3 q4 q3).symm)
  have apc7 : forall (q5 q6 q7 q8:G), ((q7 ◇ q7) ◇ q7) = ((q5 ◇ q8) ◇ q6):=by
    intro q5 q6 q7 q8
    exact (((apc6 q5 q7 q5 q8 q6).symm).trans ((apc0 (q5 ◇ q8) q7 q8 q5).symm)).symm
  exact ((apc7 x y ((x ◇ y) ◇ y) y).symm).trans (apc7 x y ((x ◇ y) ◇ y) (y ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_62470_to_61194 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_62470_to_61194
