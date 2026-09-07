-- Equation53904 → Equation53974
-- Recorded verdict: true
-- Premise: x ◇ (x ◇ y) = y ◇ (x ◇ (z ◇ z))
-- Conclusion: x ◇ (x ◇ y) = z ◇ (z ◇ (y ◇ w))
-- Original submission SHA-256: 3af2891d26f8a745a14ede41938e0cf670746a71bbab6103b6132480b302302c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ y) = y ◇ (x ◇ (z ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = z ◇ (z ◇ (y ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z:G), (y ◇ (x ◇ (z ◇ z))) = (y ◇ (x ◇ (x ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q0 ◇ q0))) = (q0 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((apc0 q0 q1 q0).symm).trans ((h q0 q1 q0).symm)
  have apc2 : forall (q2 q3 q4:G), (q4 ◇ (q2 ◇ (q2 ◇ q3))) = (q3 ◇ (q3 ◇ q4)):=by
    intro q2 q3 q4
    exact ((((congrArg (fun t => q4 ◇ t) (congrArg (fun t => q3 ◇ t) (congrArg (fun t => q2 ◇ t) (apc1 q2 q2)))).trans (congrArg (fun t => q4 ◇ t) (congrArg (fun t => q3 ◇ t) (apc1 q2 q2)))).trans (congrArg (fun t => q4 ◇ t) (apc1 q2 q3))).symm).trans (((congrArg (fun t => q4 ◇ t) (congrArg (fun t => q3 ◇ t) (apc1 q2 (q2 ◇ (q2 ◇ q2))))).symm).trans ((h q3 q4 (q2 ◇ (q2 ◇ q2))).symm))
  have apc3 : forall (q5 q6 q7:G), ((q5 ◇ q5) ◇ ((q5 ◇ q5) ◇ q7)) = (q6 ◇ (q6 ◇ q7)):=by
    intro q5 q6 q7
    exact (((apc2 q6 q6 q7).symm).trans (((congrArg (fun t => q7 ◇ t) ((h q6 q6 q5).symm)).symm).trans (apc2 q6 (q5 ◇ q5) q7))).symm
  have apc4 : forall (q5 q6 q7:G), (q6 ◇ (q6 ◇ q7)) = (q5 ◇ (q5 ◇ q7)):=by
    intro q5 q6 q7
    exact ((apc3 q5 q6 q7).symm).trans (apc3 q5 q5 q7)
  have apc5 : forall (q8 q9 q10:G), (q8 ◇ (q8 ◇ (q9 ◇ q10))) = (q10 ◇ (q10 ◇ q9)):=by
    intro q8 q9 q10
    exact ((apc4 q8 q9 (q9 ◇ q10)).symm).trans (apc2 q9 q10 q9)
  have apc6 : forall (q11 q12 q13:G), (q12 ◇ (q12 ◇ q12)) = (q11 ◇ (q11 ◇ q11)):=by
    intro q11 q12 q13
    exact ((apc5 q13 q12 q12).symm).trans (((apc4 q13 q11 (q12 ◇ q12)).symm).trans ((h q11 q11 q12).symm))
  have apc7 : forall (q14 q15 q16:G), (q16 ◇ (q16 ◇ q16)) = (q15 ◇ (q15 ◇ q14)):=by
    intro q14 q15 q16
    exact (((((((congrArg (fun t => (q14 ◇ (q15 ◇ q15)) ◇ t) (congrArg (fun t => q14 ◇ t) (apc5 q14 q15 q15))).trans (congrArg (fun t => (q14 ◇ (q15 ◇ q15)) ◇ t) (apc2 q15 q15 q14))).trans (apc2 q15 q14 (q14 ◇ (q15 ◇ q15)))).trans (congrArg (fun t => q14 ◇ t) (apc5 q14 q15 q15))).trans (apc2 q15 q15 q14)).symm).trans (((congrArg (fun t => (q14 ◇ (q15 ◇ q15)) ◇ t) ((h q14 (q14 ◇ (q15 ◇ q15)) q15).symm)).symm).trans (apc6 q16 (q14 ◇ (q15 ◇ q15)) q14))).symm
  exact ((apc7 y x (x ◇ (x ◇ y))).symm).trans (apc7 (y ◇ w) z (x ◇ (x ◇ y)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53904_to_53974 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53904_to_53974
