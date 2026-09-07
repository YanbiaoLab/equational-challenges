-- Equation25622 → Equation62245
-- Recorded verdict: true
-- Premise: x = (y * (z * (w * x))) * (u * x)
-- Conclusion: (x * y) * z = ((x * z) * y) * z
-- Original submission SHA-256: cbaa20e51ecc996f67be600db1214048c6ae0f263269a2f6728485c0b93325a0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ (z ◇ (w ◇ x))) ◇ (u ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = ((x ◇ z) ◇ y) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q1 ◇ q2) ◇ (q0 ◇ q2)) = q2:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q0 ◇ q2)) ((h (q1 ◇ q2) q0 q0 q0 q0).symm)).symm).trans ((h q2 (q0 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2)))) q0 q1 q0).symm)
  have apc1 : forall (q3 q4 q5:G), ((q5 ◇ (q3 ◇ q4)) ◇ q4) = (q3 ◇ q4):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => (q5 ◇ (q3 ◇ q4)) ◇ t) (apc0 q3 q3 q4)).symm).trans (apc0 (q3 ◇ q4) q5 (q3 ◇ q4))
  have apc2 : forall (q6 q7:G), (q7 ◇ q7) = (q6 ◇ q7):=by
    intro q6 q7
    exact ((congrArg (fun t => t ◇ q7) (apc0 q6 q6 q7)).symm).trans (apc1 q6 q7 (q6 ◇ q7))
  exact ((apc2 (x ◇ y) z).symm).trans (apc2 ((x ◇ z) ◇ y) z)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_25622_to_62245 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_25622_to_62245
