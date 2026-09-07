-- Equation15914 → Equation4993
-- Recorded verdict: true
-- Premise: x = y ◇ (((z ◇ (z ◇ z)) ◇ x) ◇ z)
-- Conclusion: x = y ◇ (x ◇ (z ◇ (y ◇ (y ◇ x))))
-- Original submission SHA-256: a4afc95d81b7b333499b1a4e32f9728ce497cf806b179900c0d7ee012b24a59d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (((z ◇ (z ◇ z)) ◇ x) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (z ◇ (y ◇ (y ◇ x))))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ q0) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) ((h q0 (((((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0) ◇ ((((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0) ◇ (((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0))) ◇ q1) q0).symm)).symm).trans ((h q1 q2 (((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0)).symm)
  exact ((apc0 x x y).symm).trans ((apc0 (x ◇ (z ◇ (y ◇ (y ◇ x)))) (y ◇ x) y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_15914_to_4993 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_15914_to_4993
