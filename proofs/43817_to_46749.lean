-- Equation43817 → Equation46749
-- Recorded verdict: true
-- Premise: x * y = z * ((x * y) * (w * x))
-- Conclusion: x * y = (z * w) * (w * (u * y))
-- Original submission SHA-256: 2a12317ae1faa74bda8adcd531f04d82100621bd7ba45d61d8bee6b96c4738d2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((x ◇ y) ◇ (w ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ w) ◇ (w ◇ (u ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q4 ◇ (q1 ◇ q2)) = ((q0 ◇ q1) ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => q4 ◇ t) ((h q1 q2 ((q0 ◇ q1) ◇ q3) q0).symm)).symm).trans ((h (q0 ◇ q1) q3 q4 (q1 ◇ q2)).symm)
  have apc1 : forall (q5 q6 q7 q8 q9:G), (q9 ◇ (q6 ◇ (q8 ◇ q5))) = (q7 ◇ q8):=by
    intro q5 q6 q7 q8 q9
    exact ((congrArg (fun t => q9 ◇ t) ((apc0 q7 q8 q5 (q5 ◇ q7) q6).symm)).symm).trans ((h q7 q8 q9 q5).symm)
  have apc12 : forall (q10 q11 q12 q13:G), (q12 ◇ q13) = (q10 ◇ q11):=by
    intro q10 q11 q12 q13
    exact (((apc1 q12 (q12 ◇ q13) q10 q11 q10).symm).trans ((h q12 q13 q10 q11).symm)).symm
  exact (apc12 (x ◇ y) ((z ◇ w) ◇ (w ◇ (u ◇ y))) x y).trans ((apc12 (x ◇ y) ((z ◇ w) ◇ (w ◇ (u ◇ y))) (z ◇ w) (w ◇ (u ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43817_to_46749 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43817_to_46749
