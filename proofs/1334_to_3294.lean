-- Equation1334 → Equation3294
-- Recorded verdict: true
-- Premise: x = y ◇ (((y ◇ z) ◇ x) ◇ z)
-- Conclusion: x ◇ x = y ◇ (z ◇ (y ◇ z))
-- Original submission SHA-256: 11e899a4fe8210b10bef7f24c6850bffddc1d363a85689dad0a69aed52809bf1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (((y ◇ z) ◇ x) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (z ◇ (y ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 : G), ((((q2 ◇ q3) ◇ q1) ◇ q0) ◇ q1) = (q2 ◇ (q0 ◇ q3)) := by
    intro q0 q1 q2 q3
    exact (((rfl).symm).trans ((((congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ q3) ((h q0 (q2 ◇ q3) q1).symm))).symm).trans ((h ((((q2 ◇ q3) ◇ q1) ◇ q0) ◇ q1) q2 q3).symm)).trans (rfl))).symm
  have apc1 : forall (q4 q5 q6 : G), ((q4 ◇ q5) ◇ (q4 ◇ (q6 ◇ q5))) = q6 := by
    intro q4 q5 q6
    exact ((rfl).symm).trans ((((congrArg (fun t => (q4 ◇ q5) ◇ t) (apc0 q6 q4 q4 q5)).symm).trans ((h q6 (q4 ◇ q5) q4).symm)).trans (rfl))
  have apc2 : forall (q7 q8 q9 q10 : G), ((q7 ◇ q8) ◇ (q9 ◇ (q7 ◇ q10))) = (q9 ◇ (q8 ◇ q10)) := by
    intro q7 q8 q9 q10
    exact ((rfl).symm).trans ((((congrArg (fun t => t ◇ (q9 ◇ (q7 ◇ q10))) (congrArg (fun t => t ◇ q8) (apc1 q9 q10 q7))).symm).trans (apc0 q8 (q9 ◇ (q7 ◇ q10)) q9 q10)).trans (rfl))
  have apc3 : forall (q11 q12 : G), (q12 ◇ (q11 ◇ q11)) = q12 := by
    intro q11 q12
    exact ((rfl).symm).trans ((((apc2 q12 q11 q12 q11).symm).trans (apc1 q12 q11 q12)).trans (rfl))
  have apc4 : forall (q13 q14 q15 : G), (q14 ◇ (q13 ◇ q15)) = ((q15 ◇ q13) ◇ q14) := by
    intro q13 q14 q15
    exact (((rfl).symm).trans ((((congrArg (fun t => (q15 ◇ q13) ◇ t) (apc3 q15 q14)).symm).trans (apc2 q15 q13 q14 q15)).trans (rfl))).symm
  have apc5 : forall (q16 q13 q15 : G), ((q16 ◇ q15) ◇ (q13 ◇ q15)) = (q16 ◇ q13) := by
    intro q16 q13 q15
    exact (((rfl).symm).trans ((((apc3 (q16 ◇ q15) (q16 ◇ q13)).symm).trans (apc2 q16 q13 (q16 ◇ q15) q15)).trans (rfl))).symm
  have apc7 : forall (q17 q18 : G), ((q17 ◇ q18) ◇ q17) = q18 := by
    intro q17 q18
    exact ((rfl).symm).trans ((((congrArg (fun t => (q17 ◇ q18) ◇ t) (apc3 q18 q17)).symm).trans (apc1 q17 q18 q18)).trans (rfl))
  have apc9 : forall (q19 q20 q21 : G), ((q19 ◇ q20) ◇ (q19 ◇ q21)) = (q20 ◇ q21) := by
    intro q19 q20 q21
    exact ((rfl).symm).trans ((((congrArg (fun t => t ◇ (q19 ◇ q21)) (apc5 q19 q20 q21)).symm).trans (apc7 (q19 ◇ q21) (q20 ◇ q21))).trans (rfl))
  have apc10 : forall (q22 q23 : G), (q23 ◇ q23) = (q22 ◇ q22) := by
    intro q22 q23
    exact ((rfl).symm).trans ((((apc9 q22 q23 q23).symm).trans (apc5 q22 q22 q23)).trans (rfl))
  exact (apc10 y x).trans (((congrArg (fun t => y ◇ t) (apc4 y z z)).trans (congrArg (fun t => y ◇ t) (apc7 z y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1334_to_3294 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_1334_to_3294
