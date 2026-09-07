-- Equation8391 → Equation13476
-- Recorded verdict: true
-- Premise: x = x * (y * (((z * w) * z) * y))
-- Conclusion: x = x * ((x * ((x * y) * z)) * x)
-- Original submission SHA-256: 45b83cb5771d7ba9b5505c09825c1c1551f398e1a112cc62b33ed448cbfb10b9
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (y ◇ (((z ◇ w) ◇ z) ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ ((x ◇ ((x ◇ y) ◇ z)) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), (q4 ◇ ((q1 ◇ (((q2 ◇ q0) ◇ q2) ◇ q1)) ◇ ((q5 ◇ q3) ◇ q5))) = q4:=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => q4 ◇ t) (congrArg (fun t => (q1 ◇ (((q2 ◇ q0) ◇ q2) ◇ q1)) ◇ t) ((h ((q5 ◇ q3) ◇ q5) q1 q2 q0).symm))).symm).trans ((h q4 (q1 ◇ (((q2 ◇ q0) ◇ q2) ◇ q1)) q5 q3).symm)
  have apc3 : forall (q6 q7 q8 q9 q10:G), (q9 ◇ ((q7 ◇ (((q8 ◇ q6) ◇ q8) ◇ q7)) ◇ (q10 ◇ q10))) = q9:=by
    intro q6 q7 q8 q9 q10
    exact ((congrArg (fun t => q9 ◇ t) (congrArg (fun t => (q7 ◇ (((q8 ◇ q6) ◇ q8) ◇ q7)) ◇ t) (congrArg (fun t => t ◇ q10) (apc0 q6 q6 q6 q6 q10 q6)))).symm).trans (apc0 q6 q7 q8 ((q6 ◇ (((q6 ◇ q6) ◇ q6) ◇ q6)) ◇ ((q6 ◇ q6) ◇ q6)) q9 q10)
  have apc4 : forall (q11 q12 q13 q14 q15 q16:G), (q15 ◇ ((((q12 ◇ q11) ◇ q12) ◇ ((q14 ◇ q13) ◇ q14)) ◇ (q16 ◇ q16))) = q15:=by
    intro q11 q12 q13 q14 q15 q16
    exact ((congrArg (fun t => q15 ◇ t) (congrArg (fun t => t ◇ (q16 ◇ q16)) ((h (((q12 ◇ q11) ◇ q12) ◇ ((q14 ◇ q13) ◇ q14)) ((q14 ◇ q13) ◇ q14) q12 q11).symm))).symm).trans (apc3 q13 (((q12 ◇ q11) ◇ q12) ◇ ((q14 ◇ q13) ◇ q14)) q14 q15 q16)
  have apc6 : forall (q17 q18:G), (q18 ◇ (q17 ◇ q17)) = q18:=by
    intro q17 q18
    exact ((congrArg (fun t => q18 ◇ t) (apc4 q17 (q17 ◇ q17) q17 q17 (q17 ◇ q17) q17)).symm).trans ((h q18 (q17 ◇ q17) ((q17 ◇ q17) ◇ q17) (q17 ◇ q17)).symm)
  have apc7 : forall (q19 q20 q21:G), (q20 ◇ ((q21 ◇ q19) ◇ q21)) = q20:=by
    intro q19 q20 q21
    exact ((congrArg (fun t => q20 ◇ t) (apc6 ((q21 ◇ q19) ◇ q21) ((q21 ◇ q19) ◇ q21))).symm).trans ((h q20 ((q21 ◇ q19) ◇ q21) q21 q19).symm)
  exact (apc7 ((x ◇ y) ◇ z) x x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_8391_to_13476 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_8391_to_13476
