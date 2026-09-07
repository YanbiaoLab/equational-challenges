-- Equation43178 → Equation58246
-- Recorded verdict: true
-- Premise: x * y = z * (w * ((y * z) * x))
-- Conclusion: (x * x) * y = x * (x * (x * z))
-- Original submission SHA-256: 04707409637f8dbc303c6c2d235905da897d19a9072509ee6f0646e80963b349
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (w ◇ ((y ◇ z) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ y = x ◇ (x ◇ (x ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), (((q1 ◇ q2) ◇ q0) ◇ q3) = (q4 ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2 q3 q4
    exact (((congrArg (fun t => q4 ◇ t) ((h q0 q1 q2 (q3 ◇ q4)).symm)).symm).trans ((h ((q1 ◇ q2) ◇ q0) q3 q4 q2).symm)).symm
  have apc1 : forall (q5 q6 q7 q8 q9:G), (q7 ◇ (q5 ◇ q6)) = (q8 ◇ q9):=by
    intro q5 q6 q7 q8 q9
    exact ((apc0 q5 q6 q5 (q5 ◇ ((q9 ◇ ((q6 ◇ q5) ◇ q5)) ◇ q8)) q7).symm).trans ((h q8 q9 ((q6 ◇ q5) ◇ q5) q5).symm)
  have apc2 : forall (q10 q11 q12 q13:G), (q12 ◇ q13) = (q10 ◇ q11):=by
    intro q10 q11 q12 q13
    exact (((apc1 q10 q10 q10 q10 q11).symm).trans (apc1 q10 q10 q10 q12 q13)).symm
  exact (apc2 ((x ◇ x) ◇ y) (x ◇ (x ◇ (x ◇ z))) (x ◇ x) y).trans ((apc2 ((x ◇ x) ◇ y) (x ◇ (x ◇ (x ◇ z))) x (x ◇ (x ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43178_to_58246 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43178_to_58246
