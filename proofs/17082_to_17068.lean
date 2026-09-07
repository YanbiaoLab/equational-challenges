-- Equation17082 → Equation17068
-- Recorded verdict: true
-- Premise: x = (x ◇ y) ◇ (y ◇ (z ◇ (x ◇ x)))
-- Conclusion: x = (x ◇ y) ◇ (y ◇ (x ◇ (z ◇ x)))
-- Original submission SHA-256: 3f27a60edf142a4bfd029f46bf4c34e01950ec3006575e3e79a2ad4ef65cb63b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ (y ◇ (z ◇ (x ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ (y ◇ (x ◇ (z ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc1 : forall (q0 q1 q2:G), (((q1 ◇ (q0 ◇ q0)) ◇ q2) ◇ (q2 ◇ q0)) = (q1 ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => ((q1 ◇ (q0 ◇ q0)) ◇ q2) ◇ t) (congrArg (fun t => q2 ◇ t) ((h q0 (q1 ◇ (q0 ◇ q0)) q1).symm))).symm).trans ((h (q1 ◇ (q0 ◇ q0)) q2 (q0 ◇ (q1 ◇ (q0 ◇ q0)))).symm)
  have apc38 : forall (q3 q4 q5 q6:G), (((q6 ◇ ((q5 ◇ q3) ◇ (q5 ◇ q3))) ◇ ((q4 ◇ (q3 ◇ q3)) ◇ q5)) ◇ (q4 ◇ (q3 ◇ q3))) = (q6 ◇ ((q5 ◇ q3) ◇ (q5 ◇ q3))):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => ((q6 ◇ ((q5 ◇ q3) ◇ (q5 ◇ q3))) ◇ ((q4 ◇ (q3 ◇ q3)) ◇ q5)) ◇ t) (apc1 q3 q4 q5)).symm).trans (apc1 (q5 ◇ q3) q6 ((q4 ◇ (q3 ◇ q3)) ◇ q5))
  have apc39 : forall (q7 q8 q9 q10:G), (((q7 ◇ q7) ◇ q10) ◇ (q10 ◇ (q9 ◇ ((q8 ◇ q7) ◇ (q8 ◇ q7))))) = (q7 ◇ q7):=by
    intro q7 q8 q9 q10
    exact ((congrArg (fun t => ((q7 ◇ q7) ◇ q10) ◇ t) (congrArg (fun t => q10 ◇ t) (apc38 q7 (q7 ◇ q7) q8 q9))).symm).trans ((h (q7 ◇ q7) q10 ((q9 ◇ ((q8 ◇ q7) ◇ (q8 ◇ q7))) ◇ (((q7 ◇ q7) ◇ (q7 ◇ q7)) ◇ q8))).symm)
  have apc43 : forall (q11 q12 q13:G), ((((q12 ◇ q11) ◇ (q12 ◇ q11)) ◇ ((q11 ◇ q11) ◇ q13)) ◇ (q11 ◇ q11)) = ((q12 ◇ q11) ◇ (q12 ◇ q11)):=by
    intro q11 q12 q13
    exact ((congrArg (fun t => (((q12 ◇ q11) ◇ (q12 ◇ q11)) ◇ ((q11 ◇ q11) ◇ q13)) ◇ t) (apc39 q11 q12 ((q12 ◇ q11) ◇ (q12 ◇ q11)) q13)).symm).trans ((h ((q12 ◇ q11) ◇ (q12 ◇ q11)) ((q11 ◇ q11) ◇ q13) q13).symm)
  have apc70 : forall (q14 q15 q16 q17:G), (((q15 ◇ q15) ◇ q17) ◇ (q17 ◇ ((q14 ◇ (q16 ◇ q15)) ◇ (q14 ◇ (q16 ◇ q15))))) = (q15 ◇ q15):=by
    intro q14 q15 q16 q17
    exact ((congrArg (fun t => ((q15 ◇ q15) ◇ q17) ◇ t) (congrArg (fun t => q17 ◇ t) (apc43 (q16 ◇ q15) q14 q14))).symm).trans (apc39 q15 q16 (((q14 ◇ (q16 ◇ q15)) ◇ (q14 ◇ (q16 ◇ q15))) ◇ (((q16 ◇ q15) ◇ (q16 ◇ q15)) ◇ q14)) q17)
  have apc71 : forall (q18 q19 q20 q21:G), (((q18 ◇ (q20 ◇ q19)) ◇ ((q19 ◇ q19) ◇ q21)) ◇ (q19 ◇ q19)) = (q18 ◇ (q20 ◇ q19)):=by
    intro q18 q19 q20 q21
    exact ((congrArg (fun t => ((q18 ◇ (q20 ◇ q19)) ◇ ((q19 ◇ q19) ◇ q21)) ◇ t) (apc70 q18 q19 q20 q21)).symm).trans ((h (q18 ◇ (q20 ◇ q19)) ((q19 ◇ q19) ◇ q21) q21).symm)
  have apc72 : forall (q22 q23 q24 q25:G), ((q24 ◇ q25) ◇ (q25 ◇ (q22 ◇ (q23 ◇ q24)))) = q24:=by
    intro q22 q23 q24 q25
    exact ((congrArg (fun t => (q24 ◇ q25) ◇ t) (congrArg (fun t => q25 ◇ t) (apc71 q22 q24 q23 q22))).symm).trans ((h q24 q25 ((q22 ◇ (q23 ◇ q24)) ◇ ((q24 ◇ q24) ◇ q22))).symm)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ y) ◇ (y ◇ (x ◇ (z ◇ x)))):=(apc72 x z x y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_17082_to_17068 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_17082_to_17068
