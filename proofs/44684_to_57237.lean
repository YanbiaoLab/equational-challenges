-- Equation44684 → Equation57237
-- Recorded verdict: true
-- Premise: x * y = z * ((x * (y * x)) * z)
-- Conclusion: x * (y * z) = (w * (z * z)) * y
-- Original submission SHA-256: 9c838d0431920399a7c50d00c72d836fbaf44081216f8c33c5ca7688346d1ba8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ ((x ◇ (y ◇ x)) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (w ◇ (z ◇ z)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (q3 ◇ ((q0 ◇ q1) ◇ q3)) = (q2 ◇ (q0 ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ q3) ((h q0 q1 q2).symm))).symm).trans ((h q2 (q0 ◇ (q1 ◇ q0)) q3).symm)
  have apc1 : forall (q4 q5 q6:G), (q4 ◇ (q5 ◇ ((q6 ◇ q5) ◇ q5))) = (q5 ◇ q6):=by
    intro q4 q5 q6
    exact ((apc0 q5 (q6 ◇ q5) q4 q4).symm).trans ((h q5 q6 q4).symm)
  have apc2 : forall (q7 q8 q9:G), (q8 ◇ (q9 ◇ q7)) = ((q7 ◇ q9) ◇ q9):=by
    intro q7 q8 q9
    exact ((congrArg (fun t => q8 ◇ t) ((h q9 q7 (q7 ◇ q9)).symm)).symm).trans (apc1 q8 (q7 ◇ q9) q9)
  have apc3 : forall (q10 q11 q12:G), ((q11 ◇ q10) ◇ q10) = (q10 ◇ q11):=by
    intro q10 q11 q12
    exact ((((((congrArg (fun t => t ◇ (q10 ◇ (q11 ◇ q10))) (congrArg (fun t => q12 ◇ t) (apc2 q10 q10 q11))).trans (congrArg (fun t => (q12 ◇ ((q10 ◇ q11) ◇ q11)) ◇ t) (apc2 q10 q10 q11))).trans (apc2 q11 (q12 ◇ ((q10 ◇ q11) ◇ q11)) (q10 ◇ q11))).trans (congrArg (fun t => t ◇ (q10 ◇ q11)) (apc2 q11 q11 q10))).trans (apc2 q11 ((q11 ◇ q10) ◇ q10) q10)).symm).trans (((apc2 q12 q12 (q10 ◇ (q11 ◇ q10))).symm).trans ((h q10 q11 q12).symm))
  have apc7 : forall (q7 q8 q9 q10 q11 q12:G), (q8 ◇ (q9 ◇ q7)) = (q9 ◇ q7):=by
    intro q7 q8 q9 q10 q11 q12
    exact (apc2 q7 q8 q9).trans (apc3 q9 q7 ((q7 ◇ q9) ◇ q9))
  have apc8 : forall (q13 q14 q15:G), ((q14 ◇ q13) ◇ q15) = (q14 ◇ q13):=by
    intro q13 q14 q15
    exact (((apc7 q13 (q15 ◇ (q14 ◇ q13)) q14 q13 q13 q13).symm).trans (apc3 (q14 ◇ q13) q15 q13)).symm
  have apc9 : forall (q16 q17 q18 q19:G), (q17 ◇ q16) = (q16 ◇ q17):=by
    intro q16 q17 q18 q19
    exact (((apc8 q17 q16 q18).symm).trans ((((apc1 ((q18 ◇ (q16 ◇ q17)) ◇ (q16 ◇ q17)) (q16 ◇ q17) q18).symm).trans (apc0 q16 q17 q19 ((q18 ◇ (q16 ◇ q17)) ◇ (q16 ◇ q17)))).trans ((congrArg (fun t => q19 ◇ t) (apc7 q16 q16 q17 (q16 ◇ (q17 ◇ q16)) (q16 ◇ (q17 ◇ q16)) (q16 ◇ (q17 ◇ q16)))).trans (apc7 q16 q19 q17 (q19 ◇ (q17 ◇ q16)) (q19 ◇ (q17 ◇ q16)) (q19 ◇ (q17 ◇ q16)))))).symm
  have apc10 : forall (q20 q21 q10 q11:G), (((q20 ◇ q21) ◇ q21) ◇ (q20 ◇ q21)) = (q10 ◇ q11):=by
    intro q20 q21 q10 q11
    exact (((congrArg (fun t => t ◇ ((q20 ◇ q21) ◇ q21)) (apc9 q20 q21 (q21 ◇ q20) (q21 ◇ q20))).trans (apc9 ((q20 ◇ q21) ◇ q21) (q20 ◇ q21) ((q20 ◇ q21) ◇ ((q20 ◇ q21) ◇ q21)) ((q20 ◇ q21) ◇ ((q20 ◇ q21) ◇ q21)))).symm).trans (((congrArg (fun t => (q21 ◇ q20) ◇ t) (apc2 q20 (q10 ◇ (q11 ◇ q10)) q21)).symm).trans ((h q10 q11 (q21 ◇ q20)).symm))
  exact ((apc10 ((w ◇ (z ◇ z)) ◇ y) (x ◇ (y ◇ z)) x (y ◇ z)).symm).trans (apc10 ((w ◇ (z ◇ z)) ◇ y) (x ◇ (y ◇ z)) (w ◇ (z ◇ z)) y)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_44684_to_57237 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_44684_to_57237
