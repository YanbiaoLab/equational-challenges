-- Equation11036 → Equation62231
-- Recorded verdict: true
-- Premise: x = x * ((y * (z * w)) * (u * v))
-- Conclusion: (x * y) * z = ((x * y) * z) * y
-- Original submission SHA-256: a462ea3d18dccc2ec489e7b0a1dcb0f12d9423158f43852b3fa4f4f1d7c642ea
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x = x ◇ ((y ◇ (z ◇ w)) ◇ (u ◇ v))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = ((x ◇ y) ◇ z) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (q1 ◇ (q2 ◇ (q3 ◇ q0))) = q1:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q1 ◇ t) ((h (q2 ◇ (q3 ◇ q0)) q0 q0 q0 q0 q0).symm)).symm).trans ((h q1 q2 q3 q0 (q0 ◇ (q0 ◇ q0)) (q0 ◇ q0)).symm)
  have apc1 : forall (q4 q5:G), (q4 ◇ q5) = q4:=by
    intro q4 q5
    exact ((congrArg (fun t => q4 ◇ t) (apc0 q4 q5 q4 q4)).symm).trans (apc0 (q4 ◇ q4) q4 q5 q4)
  exact (apc1 ((x ◇ y) ◇ z) y).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_11036_to_62231 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_11036_to_62231
