-- Equation3814 → Equation58574
-- Recorded verdict: true
-- Premise: x * y = (z * y) * (w * x)
-- Conclusion: (x * y) * y = x * (z * (z * x))
-- Original submission SHA-256: 8bbb4a6a53a6aea89efc69d955f3547654d990380c14cff9dd142b992498764e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ y) ◇ (w ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ y = x ◇ (z ◇ (z ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q1 ◇ q2) ◇ (q3 ◇ q4)) = (q4 ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ (q3 ◇ q4)) ((h q1 q2 q0 q0).symm)).symm).trans ((h q4 (q0 ◇ q1) (q0 ◇ q2) q3).symm)
  have apc3 : forall (q5 q6 q7 q8:G), (q6 ◇ (q5 ◇ q8)) = (q6 ◇ q7):=by
    intro q5 q6 q7 q8
    exact ((apc0 q5 q8 q7 q5 q6).symm).trans ((h q6 q7 q8 q5).symm)
  have apc8 : forall (q9 q10 q11 q12:G), ((q12 ◇ q11) ◇ q9) = (q10 ◇ q11):=by
    intro q9 q10 q11 q12
    exact ((apc3 q9 (q12 ◇ q11) q9 q10).symm).trans ((h q10 q11 q12 q9).symm)
  exact (apc8 y (x ◇ (z ◇ (z ◇ x))) y x).trans (apc8 y x (z ◇ (z ◇ x)) x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3814_to_58574 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3814_to_58574
