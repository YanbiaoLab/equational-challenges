-- Equation44076 → Equation41754
-- Recorded verdict: true
-- Premise: x * y = z * ((w * z) * (y * x))
-- Conclusion: x * y = x * (x * (z * (x * z)))
-- Original submission SHA-256: 02d30d10bcfe85a37038126ef7a4b86c43934b1cb932b0dd29974f18a6af7f16
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((w ◇ z) ◇ (y ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = x ◇ (x ◇ (z ◇ (x ◇ z)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q2 ◇ q1) ◇ (q0 ◇ (q3 ◇ q4))) = (q4 ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2 q3 q4
    exact (((congrArg (fun t => q4 ◇ t) ((h q1 q2 (q3 ◇ q4) q0).symm)).symm).trans ((h (q2 ◇ q1) (q0 ◇ (q3 ◇ q4)) q4 q3).symm)).symm
  have apc1 : forall (q5 q6 q7 q8:G), (q7 ◇ (q5 ◇ q6)) = (q7 ◇ q8):=by
    intro q5 q6 q7 q8
    exact ((apc0 (q5 ◇ (q6 ◇ q5)) q5 q6 q8 q7).symm).trans ((h q7 q8 (q6 ◇ q5) q5).symm)
  exact ((apc1 (x ◇ y) (x ◇ (x ◇ (z ◇ (x ◇ z)))) x y).symm).trans (apc1 (x ◇ y) (x ◇ (x ◇ (z ◇ (x ◇ z)))) x (x ◇ (z ◇ (x ◇ z))))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_44076_to_41754 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_44076_to_41754
