-- Equation52869 → Equation62009
-- Recorded verdict: true
-- Premise: x * y = ((z * (w * w)) * x) * z
-- Conclusion: (x * y) * x = ((z * y) * w) * w
-- Original submission SHA-256: d656c46c2af6ea634aa0cfe6c1a7b66a16250d6b2dab9fdfe4183e0950e942ee
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ (w ◇ w)) ◇ x) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ x = ((z ◇ y) ◇ w) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2:G), (((q1 ◇ q1) ◇ q0) ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q0) (apc0 q1 (q0 ◇ q0) q0 q0))).symm).trans ((h q0 q2 q1 q0).symm)).trans (apc0 q0 q2 (q0 ◇ q2) (q0 ◇ q2))
  have apc3 : forall (q3 q4 q5 q6:G), (((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ q5) = (q4 ◇ q4):=by
    intro q3 q4 q5 q6
    exact ((((congrArg (fun t => t ◇ q5) (congrArg (fun t => t ◇ q3) (congrArg (fun t => t ◇ (q5 ◇ q5)) (apc0 q3 (q6 ◇ q6) (q3 ◇ (q6 ◇ q6)) (q3 ◇ (q6 ◇ q6)))))).trans (congrArg (fun t => t ◇ q5) (congrArg (fun t => t ◇ q3) (apc0 (q3 ◇ q3) (q5 ◇ q5) ((q3 ◇ q3) ◇ (q5 ◇ q5)) ((q3 ◇ q3) ◇ (q5 ◇ q5)))))).trans (congrArg (fun t => t ◇ q5) (apc1 (q3 ◇ q3) q3 (((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ q3)))).symm).trans (((congrArg (fun t => t ◇ q5) (h (q5 ◇ q5) q4 q3 q6)).symm).trans (apc1 q4 q5 q6))
  have apc4 : forall (q7 q8 q9:G), ((q7 ◇ q7) ◇ q9) = (q8 ◇ q8):=by
    intro q7 q8 q9
    exact ((congrArg (fun t => t ◇ q9) (apc3 q7 q7 ((q7 ◇ q7) ◇ (q7 ◇ q7)) q7)).symm).trans (apc3 (q7 ◇ q7) q8 q9 q7)
  have apc5 : forall (q10 q11 q12 q13 q14:G), (((q10 ◇ q10) ◇ q11) ◇ q13) = ((q13 ◇ q13) ◇ q12):=by
    intro q10 q11 q12 q13 q14
    exact (((congrArg (fun t => t ◇ q13) ((apc4 q10 (q13 ◇ (q14 ◇ q14)) q11).symm)).symm).trans ((h (q13 ◇ (q14 ◇ q14)) q12 q13 q14).symm)).trans (congrArg (fun t => t ◇ q12) (apc0 q13 (q14 ◇ q14) (q13 ◇ (q14 ◇ q14)) (q13 ◇ (q14 ◇ q14))))
  have apc9 : forall (q7 q8 q9:G), ((q8 ◇ q8) ◇ q8) = ((q7 ◇ q7) ◇ q9):=by
    intro q7 q8 q9
    exact ((apc4 q7 q8 q9).trans ((apc4 q8 q8 q8).symm)).symm
  have apc10 : forall (q15 q16 q17 q18:G), (((q16 ◇ q16) ◇ q17) ◇ q18) = ((q15 ◇ q15) ◇ q15):=by
    intro q15 q16 q17 q18
    exact ((apc9 q18 q15 q15).trans ((apc5 q16 q17 q15 q18 q15).symm)).symm
  have apc23 : forall (q19 q20 q21:G), ((q20 ◇ q20) ◇ q20) = (q21 ◇ q19):=by
    intro q19 q20 q21
    exact ((h q21 q19 (q19 ◇ q19) q19).trans (apc10 q20 (q19 ◇ q19) q21 (q19 ◇ q19))).symm
  exact ((apc23 x ((x ◇ y) ◇ x) (x ◇ y)).symm).trans (apc23 w ((x ◇ y) ◇ x) ((z ◇ y) ◇ w))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52869_to_62009 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52869_to_62009
