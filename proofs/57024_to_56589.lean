-- Equation57024 → Equation56589
-- Recorded verdict: true
-- Premise: x * (y * z) = (y * (x * y)) * x
-- Conclusion: x * (x * y) = (z * (y * z)) * x
-- Original submission SHA-256: 98ee753bf9a7e57e54503ac0c142882651dd246a4313be694ae00afbb4ca3034
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = (y ◇ (x ◇ y)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ y) = (z ◇ (y ◇ z)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 : G), (q1 ◇ (q2 ◇ q3)) = (q1 ◇ (q2 ◇ q0)) := by
    intro q0 q1 q2 q3
    exact (((rfl).symm).trans (((((h q1 q2 q0).symm).symm).trans ((h q1 q2 q3).symm)).trans (rfl))).symm
  have apc1 : forall (x y z : G), (x ◇ (y ◇ z)) = (x ◇ (y ◇ x)) := by
    intro x y z
    exact ((rfl).symm).trans (((h x y z).trans ((h x y x).symm)).trans (rfl))
  have apc2 : forall (q4 q5 q6 q7 : G), ((q6 ◇ (q5 ◇ q4)) ◇ q5) = (q5 ◇ (q6 ◇ q5)) := by
    intro q4 q5 q6 q7
    exact ((rfl).symm).trans ((((congrArg (fun t => t ◇ q5) (apc0 q4 q6 q5 q6)).symm).trans ((h q5 q6 q7).symm)).trans (apc1 q5 q6 q7))
  have apc4 : forall (q8 q0 q2 q3 : G), ((q8 ◇ ((q2 ◇ q3) ◇ q8)) ◇ (q2 ◇ (q8 ◇ q2))) = ((q2 ◇ q3) ◇ (q8 ◇ q0)) := by
    intro q8 q0 q2 q3
    exact (((rfl).symm).trans (((((h (q2 ◇ q3) q8 q0).symm).symm).trans (h (q8 ◇ ((q2 ◇ q3) ◇ q8)) q2 q3)).trans (((apc2 q2 (q8 ◇ ((q2 ◇ q3) ◇ q8)) q2 ((q2 ◇ ((q8 ◇ ((q2 ◇ q3) ◇ q8)) ◇ q2)) ◇ (q8 ◇ ((q2 ◇ q3) ◇ q8)))).trans (congrArg (fun t => (q8 ◇ ((q2 ◇ q3) ◇ q8)) ◇ t) (h q2 q8 ((q2 ◇ q3) ◇ q8)))).trans (congrArg (fun t => (q8 ◇ ((q2 ◇ q3) ◇ q8)) ◇ t) (apc2 q8 q2 q8 ((q8 ◇ (q2 ◇ q8)) ◇ q2)))))).symm
  have apc6 : forall (q8 q0 q2 q3 : G), ((q2 ◇ q3) ◇ (q8 ◇ q0)) = ((q2 ◇ q3) ◇ (q8 ◇ q8)) := by
    intro q8 q0 q2 q3
    exact ((rfl).symm).trans (((apc4 q8 q0 q2 q3).symm.trans (apc4 q8 q8 q2 q3)).trans (rfl))
  have apc8 : forall (q9 q10 q11 q12 q13 : G), (q12 ◇ ((q9 ◇ (q13 ◇ q9)) ◇ q11)) = (q12 ◇ (q13 ◇ q12)) := by
    intro q9 q10 q11 q12 q13
    exact ((((h q12 q13 (q9 ◇ q10)).trans (apc2 q13 q12 q13 ((q13 ◇ (q12 ◇ q13)) ◇ q12))).symm).trans ((((congrArg (fun t => q12 ◇ t) ((h q13 q9 q10).symm)).symm).trans (apc0 q11 q12 (q9 ◇ (q13 ◇ q9)) q13)).trans (rfl))).symm
  have apc11 : forall (q14 q15 q16 q17 : G), (q16 ◇ ((q15 ◇ (q17 ◇ q14)) ◇ q16)) = (q16 ◇ (q17 ◇ q16)) := by
    intro q14 q15 q16 q17
    exact ((((h q16 q17 (q15 ◇ q17)).trans (apc2 q17 q16 q17 ((q17 ◇ (q16 ◇ q17)) ◇ q16))).symm).trans ((((congrArg (fun t => q16 ◇ t) (apc2 q14 q17 q15 q14)).symm).trans (apc1 q16 (q15 ◇ (q17 ◇ q14)) q17)).trans (rfl))).symm
  have apc21 : forall (q18 q19 q20 q21 : G), (((q21 ◇ q20) ◇ (q18 ◇ q18)) ◇ q21) = (q21 ◇ ((q21 ◇ q20) ◇ q21)) := by
    intro q18 q19 q20 q21
    exact ((congrArg (fun t => t ◇ q21) (apc6 q18 q19 q21 q20)).symm).trans ((((congrArg (fun t => t ◇ q21) ((h (q21 ◇ q20) q18 q19).symm)).symm).trans (apc2 q20 q21 (q18 ◇ ((q21 ◇ q20) ◇ q18)) q18)).trans (apc8 q18 (q21 ◇ ((q18 ◇ ((q21 ◇ q20) ◇ q18)) ◇ q21)) q21 q21 (q21 ◇ q20)))
  have apc22 : forall (q22 q23 q24 : G), (q24 ◇ (q24 ◇ q24)) = (q24 ◇ (q23 ◇ q24)) := by
    intro q22 q23 q24
    exact (((h q24 q24 ((q24 ◇ q22) ◇ q24)).trans (apc2 q24 q24 q24 ((q24 ◇ (q24 ◇ q24)) ◇ q24))).symm).trans ((((congrArg (fun t => q24 ◇ t) (apc21 q23 q22 q22 q24)).symm).trans (apc11 q23 (q24 ◇ q22) q24 q23)).trans (rfl))
  have apc23 : forall (q25 q26 q27 : G), (q27 ◇ (q26 ◇ q27)) = (q27 ◇ (q25 ◇ q27)) := by
    intro q25 q26 q27
    exact (((rfl).symm).trans ((((apc22 q25 q25 q27).symm).trans (apc22 q25 q26 q27)).trans (rfl))).symm
  have apc26 : forall (q28 q29 q30 q31 : G), ((q30 ◇ (q28 ◇ q30)) ◇ q29) = (q29 ◇ (q30 ◇ q29)) := by
    intro q28 q29 q30 q31
    exact ((rfl).symm).trans ((((congrArg (fun t => t ◇ q29) (apc23 q28 q29 q30)).symm).trans ((h q29 q30 q31).symm)).trans (apc1 q29 q30 q31))
  exact (calc
    (x ◇ (x ◇ y)) = (x ◇ (x ◇ x)) := apc1 x x y
    _ = (x ◇ (z ◇ x)) := ((apc22 x z x).symm).symm
    _ = ((z ◇ (y ◇ z)) ◇ x) := (apc26 y x z x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_57024_to_56589 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_57024_to_56589
