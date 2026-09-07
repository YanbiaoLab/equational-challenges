-- Equation24223 → Equation51784
-- Recorded verdict: true
-- Premise: x = ((y ◇ x) ◇ x) ◇ ((z ◇ z) ◇ w)
-- Conclusion: x ◇ y = ((z ◇ y) ◇ (y ◇ z)) ◇ y
-- Original submission SHA-256: f46a219f8e5e70fb7e2ab0a64236e6a8e7b73a30bd67d86c3cbee3d3fc9b2c0d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ x) ◇ x) ◇ ((z ◇ z) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ y) ◇ (y ◇ z)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (((q3 ◇ q2) ◇ q2) ◇ (q0 ◇ q1)) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => ((q3 ◇ q2) ◇ q2) ◇ t) (congrArg (fun t => t ◇ q1) ((h q0 q0 q0 q0).symm))).symm).trans ((h q2 q3 ((q0 ◇ q0) ◇ q0) q1).symm)
  have apc1 : forall (q4 q5 q6:G), (((q6 ◇ q5) ◇ q5) ◇ q4) = q5:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => ((q6 ◇ q5) ◇ q5) ◇ t) (apc0 q4 q4 q4 q4)).symm).trans (apc0 ((q4 ◇ q4) ◇ q4) (q4 ◇ q4) q5 q6)
  have apc2 : forall (q7 q8 q4 q9 q10:G), ((q4 ◇ (q7 ◇ q8)) ◇ (q9 ◇ q10)) = (q7 ◇ q8):=by
    intro q7 q8 q4 q9 q10
    exact ((congrArg (fun t => t ◇ (q9 ◇ q10)) (congrArg (fun t => t ◇ (q7 ◇ q8)) (apc0 q7 q8 q4 q7))).symm).trans (apc0 q9 q10 (q7 ◇ q8) ((q7 ◇ q4) ◇ q4))
  have apc3 : forall (q11 q12 q13 q14 q15:G), (((q11 ◇ q12) ◇ (q13 ◇ q14)) ◇ q15) = (q13 ◇ q14):=by
    intro q11 q12 q13 q14 q15
    exact ((congrArg (fun t => t ◇ q15) (congrArg (fun t => t ◇ (q13 ◇ q14)) (apc2 q11 q12 q11 q13 q14))).symm).trans (apc1 q15 (q13 ◇ q14) (q11 ◇ (q11 ◇ q12)))
  have apc5 : forall (q16 q17 q18 q19:G), (q17 ◇ q18) = (q16 ◇ q19):=by
    intro q16 q17 q18 q19
    exact (((congrArg (fun t => t ◇ q19) (apc1 (q17 ◇ q18) q16 q16)).symm).trans (apc3 (q16 ◇ q16) q16 q17 q18 q19)).symm
  exact (apc5 (x ◇ y) x y (((z ◇ y) ◇ (y ◇ z)) ◇ y)).trans ((apc5 (x ◇ y) ((z ◇ y) ◇ (y ◇ z)) y (((z ◇ y) ◇ (y ◇ z)) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_24223_to_51784 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_24223_to_51784
