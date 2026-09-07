-- Equation42851 → Equation54761
-- Recorded verdict: true
-- Premise: x * y = y * (z * ((y * x) * x))
-- Conclusion: x * (x * y) = x * ((z * y) * y)
-- Original submission SHA-256: a07a98b4c79abe85b38a9018e27a1d43fd8088b8d9c700aca61e4cf7ab62f6ed
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (z ◇ ((y ◇ x) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ y) = x ◇ ((z ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (((q2 ◇ q0) ◇ q0) ◇ q1) = (q1 ◇ (q0 ◇ q2)):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => q1 ◇ t) ((h q0 q2 (q1 ◇ ((q2 ◇ q0) ◇ q0))).symm)).symm).trans ((h ((q2 ◇ q0) ◇ q0) q1 q2).symm)).symm
  have apc1 : forall (q3 q4 q5 q6:G), (q6 ◇ ((q3 ◇ q4) ◇ (q5 ◇ q6))) = (q5 ◇ q6):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => q6 ◇ t) (apc0 q5 (q3 ◇ q4) q6)).symm).trans (((congrArg (fun t => q6 ◇ t) (apc0 q3 ((q6 ◇ q5) ◇ q5) q4)).symm).trans ((h q5 q6 ((q4 ◇ q3) ◇ q3)).symm))
  have apc2 : forall (q7 q8 q9 q10 q11:G), (q11 ◇ ((q9 ◇ q10) ◇ (q11 ◇ (q7 ◇ q8)))) = (q11 ◇ (q7 ◇ q8)):=by
    intro q7 q8 q9 q10 q11
    exact (((congrArg (fun t => q11 ◇ t) (congrArg (fun t => (q9 ◇ q10) ◇ t) (apc0 q7 q11 q8))).symm).trans (apc1 q9 q10 ((q8 ◇ q7) ◇ q7) q11)).trans (apc0 q7 q11 q8)
  have apc3 : forall (q8 q10 q12 q11:G), (q11 ◇ ((q12 ◇ q11) ◇ (q10 ◇ q8))) = (q12 ◇ q11):=by
    intro q8 q10 q12 q11
    exact ((congrArg (fun t => q11 ◇ t) (apc0 q10 (q12 ◇ q11) q8)).symm).trans (apc1 (q8 ◇ q10) q10 q12 q11)
  have apc4 : forall (q13 q14 q15 q16:G), (q16 ◇ (q13 ◇ q14)) = (q15 ◇ q16):=by
    intro q13 q14 q15 q16
    exact (((apc3 (q13 ◇ q14) q16 q15 q16).symm).trans (apc2 q13 q14 q15 q16 q16)).symm
  exact (apc4 x y (x ◇ (x ◇ y)) x).trans ((apc4 (z ◇ y) y (x ◇ (x ◇ y)) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42851_to_54761 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42851_to_54761
