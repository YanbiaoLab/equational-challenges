-- Equation22349 → Equation25029
-- Recorded verdict: true
-- Premise: x = (x * (y * y)) * ((z * y) * y)
-- Conclusion: x = (x * (y * (z * z))) * (x * w)
-- Original submission SHA-256: bb906ca92f4015f96427238bea824d2c58a2834a65290f8e32c7755c83c640c9
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (y ◇ y)) ◇ ((z ◇ y) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ (y ◇ (z ◇ z))) ◇ (x ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), ((q3 ◇ (((q2 ◇ q1) ◇ q1) ◇ ((q2 ◇ q1) ◇ q1))) ◇ (q0 ◇ ((q2 ◇ q1) ◇ q1))) = q3:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => (q3 ◇ (((q2 ◇ q1) ◇ q1) ◇ ((q2 ◇ q1) ◇ q1))) ◇ t) (congrArg (fun t => t ◇ ((q2 ◇ q1) ◇ q1)) ((h q0 q1 q2).symm))).symm).trans ((h q3 ((q2 ◇ q1) ◇ q1) (q0 ◇ (q1 ◇ q1))).symm)
  have apc1 : forall (q4 q5 q6 q7:G), ((q7 ◇ (((q6 ◇ q5) ◇ q5) ◇ ((q6 ◇ q5) ◇ q5))) ◇ q4) = q7:=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => (q7 ◇ (((q6 ◇ q5) ◇ q5) ◇ ((q6 ◇ q5) ◇ q5))) ◇ t) ((h q4 q5 q6).symm)).symm).trans (apc0 (q4 ◇ (q5 ◇ q5)) q5 q6 q7)
  have apc3 : forall (q8 q9 q10 q11 q12:G), ((q10 ◇ (q9 ◇ q9)) ◇ q8) = q10:=by
    intro q8 q9 q10 q11 q12
    exact ((congrArg (fun t => t ◇ q8) (congrArg (fun t => q10 ◇ t) (congrArg (fun t => q9 ◇ t) (apc1 (((q11 ◇ q12) ◇ q12) ◇ ((q11 ◇ q12) ◇ q12)) q12 q11 q9)))).symm).trans (((congrArg (fun t => t ◇ q8) (congrArg (fun t => q10 ◇ t) (congrArg (fun t => t ◇ ((q9 ◇ (((q11 ◇ q12) ◇ q12) ◇ ((q11 ◇ q12) ◇ q12))) ◇ (((q11 ◇ q12) ◇ q12) ◇ ((q11 ◇ q12) ◇ q12)))) (apc1 (((q11 ◇ q12) ◇ q12) ◇ ((q11 ◇ q12) ◇ q12)) q12 q11 q9)))).symm).trans (apc1 q8 (((q11 ◇ q12) ◇ q12) ◇ ((q11 ◇ q12) ◇ q12)) q9 q10))
  have apc4 : forall (q13 q14 q15:G), ((q15 ◇ q13) ◇ q14) = q15:=by
    intro q13 q14 q15
    exact ((congrArg (fun t => t ◇ q14) (congrArg (fun t => q15 ◇ t) (apc3 (q13 ◇ (q13 ◇ q13)) q13 q13 q13 q13))).symm).trans (apc3 q14 (q13 ◇ (q13 ◇ q13)) q15 q13 q13)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ (y ◇ (z ◇ z))) ◇ (x ◇ w)):=(apc4 (y ◇ (z ◇ z)) (x ◇ w) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22349_to_25029 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22349_to_25029
