-- Equation47340 → Equation56682
-- Recorded verdict: true
-- Premise: x * y = (z * x) * ((z * z) * z)
-- Conclusion: x * (y * x) = (y * (x * y)) * y
-- Original submission SHA-256: 4276c5f52e118da13b59166a25a009aa9a2009f0c97e871ab02141a57afd3b99
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ x) ◇ ((z ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (y ◇ x) = (y ◇ (x ◇ y)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ (q1 ◇ q1)) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact ((apc0 (q1 ◇ q1) ((q1 ◇ q1) ◇ q1) ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1))).symm).trans ((((congrArg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (apc0 q1 q0 q0)).symm).trans ((h q0 q2 q1).symm)).trans (apc0 q0 q2 (q0 ◇ q2)))
  have apc2 : forall (q0 q2 q1:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q2 q1
    exact (((apc1 q0 q1 q2).symm).trans (apc1 q1 q1 q2)).symm
  have apc3 : forall (q3 q4 q5:G), ((q3 ◇ q3) ◇ (q3 ◇ q3)) = ((q4 ◇ q4) ◇ q5):=by
    intro q3 q4 q5
    exact ((apc0 (q3 ◇ q3) (((q4 ◇ q4) ◇ (q4 ◇ q4)) ◇ (q4 ◇ q4)) ((q3 ◇ q3) ◇ (((q4 ◇ q4) ◇ (q4 ◇ q4)) ◇ (q4 ◇ q4)))).symm).trans (((congrArg (fun t => t ◇ (((q4 ◇ q4) ◇ (q4 ◇ q4)) ◇ (q4 ◇ q4))) (apc1 q3 q4 q3)).symm).trans ((h (q4 ◇ q4) q5 (q4 ◇ q4)).symm))
  have apc5 : forall (q6 q7 q8:G), ((q6 ◇ q6) ◇ q7) = (q8 ◇ q8):=by
    intro q6 q7 q8
    exact ((apc3 q6 q6 q7).symm).trans (apc2 q8 q6 (q6 ◇ q6))
  have apc6 : forall (q9 q10 q11:G), (q11 ◇ q11) = (q10 ◇ q9):=by
    intro q9 q10 q11
    exact ((h q10 q9 q10).trans (apc5 q10 ((q10 ◇ q10) ◇ q10) q11)).symm
  exact ((apc6 (y ◇ x) x (x ◇ (y ◇ x))).symm).trans (apc6 y (y ◇ (x ◇ y)) (x ◇ (y ◇ x)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47340_to_56682 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47340_to_56682
