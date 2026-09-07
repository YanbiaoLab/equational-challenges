-- Equation3086 → Equation41800
-- Recorded verdict: true
-- Premise: x = (((x * y) * z) * x) * y
-- Conclusion: x * y = x * (y * (z * (z * w)))
-- Original submission SHA-256: 504b3ce32e42e835ceb39ab13f1e87b53d54429b7eff38cc29f4d3cc7d8e3320
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((x ◇ y) ◇ z) ◇ x) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = x ◇ (y ◇ (z ◇ (z ◇ w)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((q1 ◇ ((q1 ◇ q2) ◇ q0)) ◇ q1) = ((q1 ◇ q2) ◇ q0):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ ((q1 ◇ q2) ◇ q0)) ((h q1 q2 q0).symm))).symm).trans ((h ((q1 ◇ q2) ◇ q0) q1 q2).symm)
  have apc1 : forall (q3 q4 q5:G), ((((q5 ◇ q4) ◇ q3) ◇ q5) ◇ ((q5 ◇ q4) ◇ q3)) = q5:=by
    intro q3 q4 q5
    exact ((congrArg (fun t => t ◇ ((q5 ◇ q4) ◇ q3)) (congrArg (fun t => t ◇ q5) (apc0 q3 q5 q4))).symm).trans ((h q5 ((q5 ◇ q4) ◇ q3) q5).symm)
  have apc4 : forall (q6 q7 q8 q9:G), (((((q8 ◇ q7) ◇ q6) ◇ q8) ◇ (q8 ◇ q9)) ◇ (((q8 ◇ q7) ◇ q6) ◇ q8)) = (q8 ◇ q9):=by
    intro q6 q7 q8 q9
    exact (((congrArg (fun t => t ◇ (((q8 ◇ q7) ◇ q6) ◇ q8)) (congrArg (fun t => (((q8 ◇ q7) ◇ q6) ◇ q8) ◇ t) (congrArg (fun t => t ◇ q9) (apc1 q6 q7 q8)))).symm).trans (apc0 q9 (((q8 ◇ q7) ◇ q6) ◇ q8) ((q8 ◇ q7) ◇ q6))).trans (congrArg (fun t => t ◇ q9) (apc1 q6 q7 q8))
  have apc5 : forall (q10 q0 q1 q2:G), (((q10 ◇ q2) ◇ (((q10 ◇ q1) ◇ q0) ◇ q10)) ◇ q1) = (((q10 ◇ q1) ◇ q0) ◇ q10):=by
    intro q10 q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ (((q10 ◇ q1) ◇ q0) ◇ q10)) (congrArg (fun t => t ◇ q2) ((h q10 q1 q0).symm)))).symm).trans ((h (((q10 ◇ q1) ◇ q0) ◇ q10) q1 q2).symm)
  have apc6 : forall (q11 q12 q13:G), (q12 ◇ (((q12 ◇ (q12 ◇ q13)) ◇ q11) ◇ q12)) = (q12 ◇ q13):=by
    intro q11 q12 q13
    exact ((congrArg (fun t => t ◇ (((q12 ◇ (q12 ◇ q13)) ◇ q11) ◇ q12)) ((h q12 (q12 ◇ q13) q11).symm)).symm).trans (apc4 q11 (q12 ◇ q13) q12 q13)
  have apc7 : forall (q14 q15 q16:G), (q15 ◇ (((q15 ◇ q15) ◇ q14) ◇ q15)) = (q15 ◇ q16):=by
    intro q14 q15 q16
    exact ((congrArg (fun t => q15 ◇ t) (apc5 q15 q14 q15 (q15 ◇ q16))).symm).trans (apc6 (((q15 ◇ q15) ◇ q14) ◇ q15) q15 q16)
  exact ((apc7 (x ◇ y) x y).symm).trans (apc7 (x ◇ y) x (y ◇ (z ◇ (z ◇ w))))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3086_to_41800 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3086_to_41800
