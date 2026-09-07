-- Equation21590 → Equation56590
-- Recorded verdict: true
-- Premise: x = (y ◇ (x ◇ x)) ◇ (z ◇ (z ◇ y))
-- Conclusion: x ◇ (x ◇ y) = (z ◇ (y ◇ z)) ◇ y
-- Original submission SHA-256: 65b253f28696456da8089fd4835160d6b717e1ed87aadc442aac8cf7475cad06
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ x)) ◇ (z ◇ (z ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ y) = (z ◇ (y ◇ z)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ (q2 ◇ (q2 ◇ q1))) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q2 ◇ (q2 ◇ q1))) (congrArg (fun t => q1 ◇ t) ((h q0 q0 q0).symm))).symm).trans ((h (q0 ◇ (q0 ◇ q0)) q1 q2).symm)
  have apc1 : forall (q3 q4 q5:G), ((((q4 ◇ (q3 ◇ q3)) ◇ q4) ◇ q5) ◇ q3) = (q5 ◇ (q5 ◇ q5)):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => (((q4 ◇ (q3 ◇ q3)) ◇ q4) ◇ q5) ◇ t) ((h q3 q4 (q4 ◇ (q3 ◇ q3))).symm)).symm).trans (apc0 q5 ((q4 ◇ (q3 ◇ q3)) ◇ q4) (q4 ◇ (q3 ◇ q3)))
  have apc2 : forall (q6 q0 q7:G), ((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ (q6 ◇ q6))) = q6:=by
    intro q6 q0 q7
    exact ((apc1 q0 q7 (q6 ◇ q6)).symm).trans (((congrArg (fun t => (((q7 ◇ (q0 ◇ q0)) ◇ q7) ◇ (q6 ◇ q6)) ◇ t) ((h q0 q7 (q7 ◇ (q0 ◇ q0))).symm)).symm).trans ((h q6 ((q7 ◇ (q0 ◇ q0)) ◇ q7) (q7 ◇ (q0 ◇ q0))).symm))
  have apc3 : forall (q8 q9:G), (((q8 ◇ q8) ◇ q9) ◇ q8) = (q9 ◇ (q9 ◇ q9)):=by
    intro q8 q9
    exact ((congrArg (fun t => ((q8 ◇ q8) ◇ q9) ◇ t) (apc2 q8 q8 q8)).symm).trans (apc0 q9 (q8 ◇ q8) (q8 ◇ q8))
  have apc4 : forall (q10:G), (q10 ◇ q10) = q10:=by
    intro q10
    exact ((congrArg (fun t => t ◇ q10) (apc2 q10 ((q10 ◇ q10) ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10))) ((q10 ◇ q10) ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10))))).symm).trans ((((congrArg (fun t => t ◇ q10) (apc3 (q10 ◇ q10) (q10 ◇ q10))).symm).trans (apc1 q10 (q10 ◇ q10) (q10 ◇ q10))).trans (apc2 q10 ((q10 ◇ q10) ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10))) ((q10 ◇ q10) ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10)))))
  have apc6 : forall (q8 q9 q10:G), ((q8 ◇ q9) ◇ q8) = q9:=by
    intro q8 q9 q10
    exact ((congrArg (fun t => t ◇ q8) (congrArg (fun t => t ◇ q9) (apc4 q8))).symm).trans ((apc3 q8 q9).trans ((congrArg (fun t => q9 ◇ t) (apc4 q9)).trans (apc4 q9)))
  have apc7 : forall (q11 q12:G), (q11 ◇ (q12 ◇ q11)) = q12:=by
    intro q11 q12
    exact ((congrArg (fun t => t ◇ (q12 ◇ q11)) (apc6 q12 q11 q11)).symm).trans (apc6 (q12 ◇ q11) q12 q11)
  have apc8 : forall (q13 q14 q15:G), ((q15 ◇ (q15 ◇ q14)) ◇ q13) = (q14 ◇ q13):=by
    intro q13 q14 q15
    exact (((congrArg (fun t => (q15 ◇ (q15 ◇ q14)) ◇ t) ((h q13 q14 q15).symm)).symm).trans (apc7 (q15 ◇ (q15 ◇ q14)) (q14 ◇ (q13 ◇ q13)))).trans (congrArg (fun t => q14 ◇ t) (apc4 q13))
  have apc9 : forall (q16 q17 q18:G), (q17 ◇ (q17 ◇ q16)) = q16:=by
    intro q16 q17 q18
    exact (((apc7 q18 q16).symm).trans (((congrArg (fun t => q18 ◇ t) (apc8 q18 q16 q17)).symm).trans (apc7 q18 (q17 ◇ (q17 ◇ q16))))).symm
  exact (calc
    (x ◇ (x ◇ y)) = y:=apc9 y x (x ◇ (x ◇ y))
    _ = ((z ◇ (y ◇ z)) ◇ y):=((congrArg (fun t => t ◇ y) (apc7 z y)).trans (apc4 y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_21590_to_56590 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_21590_to_56590
