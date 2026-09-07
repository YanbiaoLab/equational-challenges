-- Equation29959 → Equation56946
-- Recorded verdict: true
-- Premise: x = (y * (z * (z * (z * w)))) * w
-- Conclusion: x * (y * z) = (x * (x * x)) * w
-- Original submission SHA-256: 26ab472251035a43e4e13ca1af801a20085fb7a0f861f612b28165969cdcf1df
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ (z ◇ (z ◇ w)))) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (x ◇ (x ◇ x)) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q0 ◇ q1) = q2:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) ((h q0 q0 q0 (q0 ◇ (q0 ◇ (q0 ◇ q1)))).symm)).symm).trans ((h q2 (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1))))))) q0 q1).symm)
  exact (apc0 x (y ◇ z) (x ◇ (y ◇ z))).trans ((apc0 (x ◇ (x ◇ x)) w (x ◇ (y ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_29959_to_56946 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_29959_to_56946
