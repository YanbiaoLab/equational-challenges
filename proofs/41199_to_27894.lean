-- Equation41199 → Equation27894
-- Recorded verdict: true
-- Premise: x = ((((y * z) * x) * z) * z) * x
-- Conclusion: x = ((y * (y * y)) * x) * (z * x)
-- Original submission SHA-256: 3c219a685d80abc8df7ad433620434bc08ae170940a9667d0368d72085abd6cd
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((((y ◇ z) ◇ x) ◇ z) ◇ z) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ (y ◇ y)) ◇ x) ◇ (z ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), (((q0 ◇ q1) ◇ q1) ◇ q0) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q0) (congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q1) ((h q0 q0 q1).symm)))).symm).trans ((h q0 (((q0 ◇ q1) ◇ q0) ◇ q1) q1).symm)
  have apc2 : forall (q1:G), (q1 ◇ q1) = q1:=by
    intro q1
    exact ((congrArg (fun t => t ◇ q1) ((h q1 q1 q1).symm)).symm).trans ((h q1 (q1 ◇ q1) q1).symm)
  have apc4 : forall (q2 q3:G), (q3 ◇ ((q3 ◇ q2) ◇ q2)) = ((q3 ◇ q2) ◇ q2):=by
    intro q2 q3
    exact ((congrArg (fun t => t ◇ ((q3 ◇ q2) ◇ q2)) (apc2 q3)).symm).trans (((congrArg (fun t => t ◇ ((q3 ◇ q2) ◇ q2)) (congrArg (fun t => t ◇ q3) (apc0 q3 q2))).symm).trans (apc0 ((q3 ◇ q2) ◇ q2) q3))
  have apc5 : forall (q4 q5:G), (q5 ◇ (((q4 ◇ q5) ◇ q5) ◇ q5)) = (((q4 ◇ q5) ◇ q5) ◇ q5):=by
    intro q4 q5
    exact ((congrArg (fun t => t ◇ (((q4 ◇ q5) ◇ q5) ◇ q5)) ((h q5 q4 q5).symm)).symm).trans (apc0 (((q4 ◇ q5) ◇ q5) ◇ q5) q5)
  have apc6 : forall (q6 q7:G), ((((q6 ◇ q7) ◇ q7) ◇ q7) ◇ q7) = q7:=by
    intro q6 q7
    exact ((congrArg (fun t => t ◇ q7) (apc2 (((q6 ◇ q7) ◇ q7) ◇ q7))).symm).trans (((congrArg (fun t => t ◇ q7) (congrArg (fun t => t ◇ (((q6 ◇ q7) ◇ q7) ◇ q7)) (apc5 q6 q7))).symm).trans (apc0 q7 (((q6 ◇ q7) ◇ q7) ◇ q7)))
  have apc8 : forall (q8 q9:G), (((q8 ◇ q9) ◇ q9) ◇ q9) = q9:=by
    intro q8 q9
    exact (((congrArg (fun t => ((q8 ◇ q9) ◇ q9) ◇ t) (apc6 q8 q9)).symm).trans (apc4 q9 ((q8 ◇ q9) ◇ q9))).trans (apc6 q8 q9)
  have apc9 : forall (q10 q11:G), ((q10 ◇ q11) ◇ q11) = q11:=by
    intro q10 q11
    exact (((congrArg (fun t => (q10 ◇ q11) ◇ t) (apc8 q10 q11)).symm).trans (apc4 q11 (q10 ◇ q11))).trans (apc8 q10 q11)
  have apc10 : forall (q0 q1 q10 q11:G), (q1 ◇ q0) = q0:=by
    intro q0 q1 q10 q11
    exact ((congrArg (fun t => t ◇ q0) (apc9 q0 q1)).symm).trans (apc0 q0 q1)
  exact ((apc10 x z x x).symm).trans ((apc10 (z ◇ x) ((y ◇ (y ◇ y)) ◇ x) x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41199_to_27894 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41199_to_27894
