-- Equation32878 → Equation18757
-- Recorded verdict: true
-- Premise: x = (x * (((y * y) * z) * z)) * z
-- Conclusion: x = (x * x) * ((y * y) * (y * z))
-- Original submission SHA-256: a65ee2f6d272ed696886875eba6694a4ea3d1b43eac2cccadc353bf8c4064d79
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (((y ◇ y) ◇ z) ◇ z)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ x) ◇ ((y ◇ y) ◇ (y ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc4 : forall (q0 q1 q2 q3:G), (q0 ◇ (((q1 ◇ q1) ◇ (((q2 ◇ q2) ◇ q3) ◇ q3)) ◇ (((q2 ◇ q2) ◇ q3) ◇ q3))) = (q0 ◇ q3):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => t ◇ q3) ((h q0 q1 (((q2 ◇ q2) ◇ q3) ◇ q3)).symm)).symm).trans ((h (q0 ◇ (((q1 ◇ q1) ◇ (((q2 ◇ q2) ◇ q3) ◇ q3)) ◇ (((q2 ◇ q2) ◇ q3) ◇ q3))) q2 q3).symm)).symm
  have apc6 : forall (q4 q5 q6:G), ((q6 ◇ q5) ◇ (((q4 ◇ q4) ◇ q5) ◇ q5)) = q6:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => t ◇ (((q4 ◇ q4) ◇ q5) ◇ q5)) (apc4 q6 q4 q4 q5)).symm).trans ((h q6 q4 (((q4 ◇ q4) ◇ q5) ◇ q5)).symm)
  have apc7 : forall (q7 q8 q9 q10:G), ((q10 ◇ q9) ◇ ((((q7 ◇ q7) ◇ q8) ◇ q9) ◇ q9)) = q10:=by
    intro q7 q8 q9 q10
    exact ((congrArg (fun t => (q10 ◇ q9) ◇ t) (congrArg (fun t => t ◇ q9) (congrArg (fun t => t ◇ q9) (apc6 q7 q8 ((q7 ◇ q7) ◇ q8))))).symm).trans (apc6 (((q7 ◇ q7) ◇ q8) ◇ q8) q9 q10)
  have apc8 : forall (q11 q12 q13:G), ((q13 ◇ q12) ◇ ((q11 ◇ q12) ◇ q12)) = q13:=by
    intro q11 q12 q13
    exact ((congrArg (fun t => (q13 ◇ q12) ◇ t) (congrArg (fun t => t ◇ q12) (congrArg (fun t => t ◇ q12) (apc6 q11 q11 q11)))).symm).trans (apc7 q11 (((q11 ◇ q11) ◇ q11) ◇ q11) q12 q13)
  have apc9 : forall (q14 q15 q16:G), ((q16 ◇ q15) ◇ ((q14 ◇ q14) ◇ q15)) = q16:=by
    intro q14 q15 q16
    exact ((congrArg (fun t => (q16 ◇ q15) ◇ t) (congrArg (fun t => t ◇ q15) ((h (q14 ◇ q14) q14 q15).symm))).symm).trans (apc7 q14 (((q14 ◇ q14) ◇ q15) ◇ q15) q15 q16)
  have apc10 : forall (q17 q18 q19 q20:G), ((q20 ◇ q19) ◇ ((q17 ◇ q18) ◇ q19)) = q20:=by
    intro q17 q18 q19 q20
    exact ((congrArg (fun t => (q20 ◇ q19) ◇ t) (congrArg (fun t => t ◇ q19) (apc8 q17 q18 (q17 ◇ q18)))).symm).trans (apc9 ((q17 ◇ q18) ◇ q18) q19 q20)
  have apc12 : forall (q21 q22 q23:G), ((q23 ◇ q22) ◇ q21) = q23:=by
    intro q21 q22 q23
    exact ((congrArg (fun t => (q23 ◇ q22) ◇ t) ((h q21 q21 q22).symm)).symm).trans (apc10 q21 (((q21 ◇ q21) ◇ q22) ◇ q22) q22 q23)
  exact (apc12 ((y ◇ y) ◇ (y ◇ z)) x x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32878_to_18757 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_32878_to_18757
