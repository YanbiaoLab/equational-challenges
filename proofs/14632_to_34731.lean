-- Equation14632 → Equation34731
-- Recorded verdict: true
-- Premise: x = y * (((x * z) * (x * w)) * y)
-- Conclusion: x = ((y * x) * ((x * y) * y)) * z
-- Original submission SHA-256: c3198e859d0d7d1bac38a8d0e69732b83f822cd94492e80f40cad9b09e923c6c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (((x ◇ z) ◇ (x ◇ w)) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ ((x ◇ y) ◇ y)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), ((((q1 ◇ q2) ◇ (q1 ◇ q0)) ◇ ((q4 ◇ q5) ◇ (q4 ◇ q3))) ◇ q1) = q4:=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => (((q1 ◇ q2) ◇ (q1 ◇ q0)) ◇ ((q4 ◇ q5) ◇ (q4 ◇ q3))) ◇ t) ((h q1 ((q4 ◇ q5) ◇ (q4 ◇ q3)) q2 q0).symm)).symm).trans ((h q4 (((q1 ◇ q2) ◇ (q1 ◇ q0)) ◇ ((q4 ◇ q5) ◇ (q4 ◇ q3))) q5 q3).symm)
  have apc1 : forall (q6 q7 q8 q9 q10 q11:G), (((q6 ◇ (q8 ◇ q7)) ◇ ((q10 ◇ q11) ◇ (q10 ◇ q9))) ◇ q8) = q10:=by
    intro q6 q7 q8 q9 q10 q11
    exact ((congrArg (fun t => t ◇ q8) (congrArg (fun t => t ◇ ((q10 ◇ q11) ◇ (q10 ◇ q9))) (congrArg (fun t => t ◇ (q8 ◇ q7)) ((h q6 q8 q6 q6).symm)))).symm).trans (apc0 q7 q8 (((q6 ◇ q6) ◇ (q6 ◇ q6)) ◇ q8) q9 q10 q11)
  have apc2 : forall (q12 q13 q14 q15 q16 q17:G), (((q13 ◇ q12) ◇ ((q16 ◇ q17) ◇ (q16 ◇ q15))) ◇ q14) = q16:=by
    intro q12 q13 q14 q15 q16 q17
    exact ((congrArg (fun t => t ◇ q14) (congrArg (fun t => t ◇ ((q16 ◇ q17) ◇ (q16 ◇ q15))) (congrArg (fun t => q13 ◇ t) ((h q12 q14 q12 q12).symm)))).symm).trans (apc1 q13 (((q12 ◇ q12) ◇ (q12 ◇ q12)) ◇ q14) q14 q15 q16 q17)
  have apc3 : forall (q18 q19 q20 q21 q22 q23:G), (((q20 ◇ q19) ◇ ((q22 ◇ q23) ◇ q18)) ◇ q21) = q22:=by
    intro q18 q19 q20 q21 q22 q23
    exact ((congrArg (fun t => t ◇ q21) (congrArg (fun t => (q20 ◇ q19) ◇ t) (congrArg (fun t => (q22 ◇ q23) ◇ t) ((h q18 q22 q18 q18).symm)))).symm).trans (apc2 q19 q20 q21 (((q18 ◇ q18) ◇ (q18 ◇ q18)) ◇ q22) q22 q23)
  exact (calc
    x = x:=rfl
    _ = (((y ◇ x) ◇ ((x ◇ y) ◇ y)) ◇ z):=(apc3 y x y z x y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_14632_to_34731 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_14632_to_34731
