-- Equation40690 → Equation43602
-- Recorded verdict: true
-- Premise: x = ((((x * x) * y) * z) * x) * w
-- Conclusion: x * y = x * ((z * z) * (z * x))
-- Original submission SHA-256: 371776582801a7cd9ea0e2e5fec76f3542c13416255cb7ae7fef43b5c4dee2bb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((((x ◇ x) ◇ y) ◇ z) ◇ x) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = x ◇ ((z ◇ z) ◇ (z ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), (q1 ◇ q1) = (q1 ◇ q0):=by
    intro q0 q1
    exact (((congrArg (fun t => t ◇ q0) ((h q1 (q1 ◇ q1) q0 (q1 ◇ q1)).symm)).symm).trans ((h (q1 ◇ q1) q0 q1 q0).symm)).symm
  exact ((apc0 y x).symm).trans (apc0 ((z ◇ z) ◇ (z ◇ x)) x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_40690_to_43602 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_40690_to_43602
