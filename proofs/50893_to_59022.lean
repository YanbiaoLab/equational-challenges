-- Equation50893 → Equation59022
-- Recorded verdict: true
-- Premise: x * y = (z * ((y * x) * w)) * x
-- Conclusion: (x * y) * z = w * (w * (w * y))
-- Original submission SHA-256: 5e4dac437e0ac0ad355ff4861123a26616d847ba0d0392b0ef84ae377bf00e40
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ ((y ◇ x) ◇ w)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = w ◇ (w ◇ (w ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), (q4 ◇ (q2 ◇ ((q1 ◇ q4) ◇ q0))) = ((q5 ◇ ((q4 ◇ q1) ◇ q3)) ◇ q4):=by
    intro q0 q1 q2 q3 q4 q5
    exact (((congrArg (fun t => t ◇ q4) (congrArg (fun t => q5 ◇ t) (congrArg (fun t => t ◇ q3) ((h q4 q1 q2 q0).symm)))).symm).trans ((h q4 (q2 ◇ ((q1 ◇ q4) ◇ q0)) q5 q3).symm)).symm
  have apc1 : forall (q6 q7 q8:G), (q8 ◇ (q7 ◇ ((q8 ◇ q8) ◇ q6))) = (q8 ◇ q8):=by
    intro q6 q7 q8
    exact (apc0 q6 q8 q7 q6 q8 q6).trans ((h q8 q8 q6 q6).symm)
  have apc2 : forall (q9 q10 q11:G), ((q11 ◇ q11) ◇ q9) = (q9 ◇ q10):=by
    intro q9 q10 q11
    exact ((congrArg (fun t => t ◇ q9) (apc1 q9 (q10 ◇ q9) q11)).symm).trans ((h q9 q10 q11 ((q11 ◇ q11) ◇ q9)).symm)
  have apc7 : forall (q9 q10 q11:G), (q9 ◇ q10) = (q9 ◇ q9):=by
    intro q9 q10 q11
    exact ((apc2 q9 q10 q11).symm).trans (apc2 q9 q9 q11)
  have apc8 : forall (q1 q3 q4 q12:G), ((((q12 ◇ q4) ◇ q3) ◇ q1) ◇ q4) = (q4 ◇ q4):=by
    intro q1 q3 q4 q12
    exact (((congrArg (fun t => t ◇ q4) ((h ((q12 ◇ q4) ◇ q3) q1 q1 q1).symm)).symm).trans ((h q4 q12 (q1 ◇ ((q1 ◇ ((q12 ◇ q4) ◇ q3)) ◇ q1)) q3).symm)).trans (apc7 q4 q12 (q4 ◇ q12))
  have apc9 : forall (q13 q14 q15:G), ((q14 ◇ q13) ◇ q15) = (q15 ◇ q15):=by
    intro q13 q14 q15
    exact ((congrArg (fun t => t ◇ q15) ((h q14 q13 (q13 ◇ q15) q13).symm)).symm).trans (apc8 q14 ((q13 ◇ q14) ◇ q13) q15 q13)
  have apc13 : forall (q16 q17 q18 q19:G), ((q17 ◇ q17) ◇ (q17 ◇ q17)) = (q18 ◇ q16):=by
    intro q16 q17 q18 q19
    exact ((((apc2 q18 q16 q17).symm).trans ((apc2 (q17 ◇ q17) q18 q19).symm)).trans (apc9 q19 q19 (q17 ◇ q17))).symm
  exact ((apc13 z ((x ◇ y) ◇ z) (x ◇ y) ((x ◇ y) ◇ z)).symm).trans (apc13 (w ◇ (w ◇ y)) ((x ◇ y) ◇ z) w ((x ◇ y) ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50893_to_59022 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_50893_to_59022
