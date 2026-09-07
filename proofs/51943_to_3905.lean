-- Equation51943 → Equation3905
-- Recorded verdict: true
-- Premise: x * y = ((z * w) * (y * y)) * x
-- Conclusion: x * x = (y * (z * z)) * x
-- Original submission SHA-256: 32bc1a7e5aa2e5e5142f44427780e0245e4444b5fb613e2030811e4fffcc5837
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ w) ◇ (y ◇ y)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (y ◇ (z ◇ z)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (((q2 ◇ q2) ◇ q0) ◇ q1) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) ((h (q2 ◇ q2) q0 q0 q0).symm)).symm).trans ((h q1 q2 (q0 ◇ q0) (q0 ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5:G), (q4 ◇ q5) = (q4 ◇ q3):=by
    intro q3 q4 q5
    exact (((apc0 (q5 ◇ q5) q4 q3).symm).trans ((h q4 q5 q3 q3).symm)).symm
  have apc2 : forall (q3 q4 q5:G), (q4 ◇ q4) = (q4 ◇ q3):=by
    intro q3 q4 q5
    exact (((apc1 q3 q4 q5).symm).trans (apc1 q4 q4 q5)).symm
  have apc3 : forall (q6 q7 q8 q9:G), (((q9 ◇ q6) ◇ (q9 ◇ q6)) ◇ q7) = (q7 ◇ q8):=by
    intro q6 q7 q8 q9
    exact ((congrArg (fun t => t ◇ q7) ((apc2 (q8 ◇ q8) (q9 ◇ q6) q6).symm)).symm).trans ((h q7 q8 q9 q6).symm)
  have apc4 : forall (q10 q11 q12 q13 q14:G), ((q12 ◇ (q11 ◇ q10)) ◇ q13) = (q13 ◇ q14):=by
    intro q10 q11 q12 q13 q14
    exact ((congrArg (fun t => t ◇ q13) (apc0 q14 q12 (q11 ◇ q10))).symm).trans (((congrArg (fun t => t ◇ q13) (congrArg (fun t => t ◇ q12) ((apc3 q10 q14 q14 q11).symm))).symm).trans (apc0 q12 q13 q14))
  have apc6 : forall (q15 q16 q17 q18:G), ((q16 ◇ (q15 ◇ q15)) ◇ q17) = (q17 ◇ q18):=by
    intro q15 q16 q17 q18
    exact ((congrArg (fun t => t ◇ q17) (congrArg (fun t => q16 ◇ t) ((apc2 q15 q15 q15).symm))).symm).trans (apc4 q15 q15 q16 q17 q18)
  have apc7 : forall (q19 q20 q21:G), ((q20 ◇ (q19 ◇ q19)) ◇ q21) = (q21 ◇ q21):=by
    intro q19 q20 q21
    exact (apc6 q19 q20 q21 q19).trans ((apc2 q19 q21 q19).symm)
  exact (calc
    (x ◇ x) = (x ◇ x):=rfl
    _ = ((y ◇ (z ◇ z)) ◇ x):=(apc7 z y x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51943_to_3905 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51943_to_3905
