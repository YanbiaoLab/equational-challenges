-- Equation3186 → Equation1457
-- Recorded verdict: true
-- Premise: x = (((y * z) * x) * z) * z
-- Conclusion: x = (x * y) * (y * (z * x))
-- Original submission SHA-256: ed469dd646b78bc3ec4b6122ef86ad68aa5f63b3ecf1ca526724580da9383f4b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((y ◇ z) ◇ x) ◇ z) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ (y ◇ (z ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), ((q0 ◇ q1) ◇ q1) = q1:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q1) ((h q0 q0 q1).symm))).symm).trans ((h q1 ((q0 ◇ q1) ◇ q0) q1).symm)
  have apc2 : forall (q2 q3:G), q3 = q2:=by
    intro q2 q3
    exact ((apc0 ((q2 ◇ q3) ◇ q2) q3).symm).trans ((h q2 q2 q3).symm)
  exact (apc2 x x).trans ((apc2 x ((x ◇ y) ◇ (y ◇ (z ◇ x)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3186_to_1457 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3186_to_1457
