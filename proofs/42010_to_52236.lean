-- Equation42010 → Equation52236
-- Recorded verdict: true
-- Premise: x * y = y * (z * (w * (x * z)))
-- Conclusion: x * x = ((y * (z * w)) * y) * y
-- Original submission SHA-256: e6fe2b713b412c887ebf80884386f11332584b02cff9916fe109c2f9c758d9f4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (z ◇ (w ◇ (x ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = ((y ◇ (z ◇ w)) ◇ y) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (q3 ◇ (q0 ◇ (q0 ◇ q1))) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q3 ◇ t) ((h q0 (q0 ◇ q1) q1 q2).symm)).symm).trans ((h q2 q3 (q0 ◇ q1) q1).symm)
  have apc2 : forall (q4 q5 q6 q7:G), (q7 ◇ (q4 ◇ q5)) = (q6 ◇ q7):=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => q7 ◇ t) (apc0 q5 q4 q4 q5)).symm).trans (apc0 q5 (q5 ◇ q4) q6 q7)
  have apc3 : forall (q8 q9 q10 q11 q12 q13:G), ((q8 ◇ q9) ◇ (q11 ◇ q12)) = (q10 ◇ q13):=by
    intro q8 q9 q10 q11 q12 q13
    exact (((apc2 q8 q9 q10 q13).symm).trans ((apc2 q11 q12 q13 (q8 ◇ q9)).symm)).symm
  have apc4 : forall (q8 q9 q10 q11 q12 q13:G), (q10 ◇ q13) = (q8 ◇ q8):=by
    intro q8 q9 q10 q11 q12 q13
    exact ((apc3 q8 q9 q10 q11 q12 q13).symm).trans (apc3 q8 q9 q8 q11 q12 q8)
  exact (apc4 (x ◇ x) (x ◇ x) x (x ◇ x) (x ◇ x) x).trans ((apc4 (x ◇ x) (x ◇ x) ((y ◇ (z ◇ w)) ◇ y) (x ◇ x) (x ◇ x) y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42010_to_52236 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42010_to_52236
