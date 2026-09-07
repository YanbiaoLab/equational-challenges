-- Equation37281 → Equation27626
-- Recorded verdict: true
-- Premise: x = ((x * (y * (z * x))) * z) * w
-- Conclusion: x = ((x * (y * z)) * x) * (x * w)
-- Original submission SHA-256: b61c2bfefcec2c39f696ba5129b8ba4cbd8f8b7bc9836d3c155ab272d8ab4ce4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((x ◇ (y ◇ (z ◇ x))) ◇ z) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((x ◇ (y ◇ z)) ◇ x) ◇ (x ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (((q2 ◇ q0) ◇ q3) ◇ q1) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q3) (congrArg (fun t => q2 ◇ t) ((h q0 q0 q0 (q3 ◇ q2)).symm)))).symm).trans ((h q2 ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ q0) q3 q1).symm)
  exact (calc
    x = x:=rfl
    _ = (((x ◇ (y ◇ z)) ◇ x) ◇ (x ◇ w)):=(apc0 (y ◇ z) (x ◇ w) x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_37281_to_27626 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_37281_to_27626
