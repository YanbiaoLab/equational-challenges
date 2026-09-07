-- Equation56190 → Equation53920
-- Recorded verdict: true
-- Premise: x * (y * z) = (y * z) * (w * y)
-- Conclusion: x * (x * y) = y * (z * (y * x))
-- Original submission SHA-256: 68ac68140b139e1a053761a797ee2952d8b056ed01c7e07643fdd049b84a9c15
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (y ◇ z) ◇ (w ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ y) = y ◇ (z ◇ (y ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc1 : forall (x y z w:G), (y ◇ (y ◇ z)) = (x ◇ (y ◇ z)):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc3 : forall (q0 q1 q2 q3:G), (q1 ◇ (q2 ◇ q3)) = (q0 ◇ (q0 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact ((apc1 (q2 ◇ q3) q0 q2 q0).trans ((h q1 q2 q3 q0).symm)).symm
  have apc12 : forall (q4 q5 q6 q7 q8:G), (q6 ◇ (q7 ◇ q8)) = (q4 ◇ (q4 ◇ q5)):=by
    intro q4 q5 q6 q7 q8
    exact (((apc3 q4 q5 q5 q7).symm).trans ((apc3 q5 q6 q7 q8).symm)).symm
  exact (apc12 (x ◇ (x ◇ y)) (y ◇ (z ◇ (y ◇ x))) x x y).trans ((apc12 (x ◇ (x ◇ y)) (y ◇ (z ◇ (y ◇ x))) y z (y ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_56190_to_53920 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_56190_to_53920
