-- Equation22827 → Equation13979
-- Recorded verdict: true
-- Premise: x = (y ◇ (z ◇ y)) ◇ ((x ◇ z) ◇ z)
-- Conclusion: x = y ◇ ((z ◇ ((x ◇ x) ◇ z)) ◇ y)
-- Original submission SHA-256: 63baeb14f6166cd7f1706c9674fdd4d44f67f2adf95cd344d2e4c02bfdadb8be
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ y)) ◇ ((x ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ ((x ◇ x) ◇ z)) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc1 : forall (x y z : G), ((y ◇ (z ◇ y)) ◇ ((x ◇ z) ◇ z)) = ((x ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ x)) := by
    intro x y z
    exact ((rfl).symm).trans (((h x y z).symm.trans (h x x x)).trans (rfl))
  have apc2 : forall (q0 : G), ((q0 ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ q0)) = q0 := by
    intro q0
    exact ((rfl).symm).trans ((((apc1 q0 q0 q0).symm).trans ((h q0 q0 q0).symm)).trans (rfl))
  have apc3 : forall (q1 q2 q3 q4 : G), ((q4 ◇ (((q1 ◇ q3) ◇ q3) ◇ q4)) ◇ (q1 ◇ ((q1 ◇ q3) ◇ q3))) = (q2 ◇ (q3 ◇ q2)) := by
    intro q1 q2 q3 q4
    exact ((rfl).symm).trans ((((congrArg (fun t => (q4 ◇ (((q1 ◇ q3) ◇ q3) ◇ q4)) ◇ t) (congrArg (fun t => t ◇ ((q1 ◇ q3) ◇ q3)) ((h q1 q2 q3).symm))).symm).trans ((h (q2 ◇ (q3 ◇ q2)) q4 ((q1 ◇ q3) ◇ q3)).symm)).trans (rfl))
  have apc4 : forall (q1 q2 q3 q4 : G), (q2 ◇ (q3 ◇ q2)) = (q1 ◇ (q3 ◇ q1)) := by
    intro q1 q2 q3 q4
    exact ((rfl).symm).trans (((apc3 q1 q2 q3 q4).symm.trans (apc3 q1 q1 q3 q4)).trans (rfl))
  have apc6 : forall (q5 q6 q7 q8 : G), (q8 ◇ ((q6 ◇ (q7 ◇ q6)) ◇ q8)) = (((q5 ◇ q7) ◇ q7) ◇ q5) := by
    intro q5 q6 q7 q8
    exact (((rfl).symm).trans ((((congrArg (fun t => ((q5 ◇ q7) ◇ q7) ◇ t) ((h q5 q6 q7).symm)).symm).trans (apc4 q8 ((q5 ◇ q7) ◇ q7) (q6 ◇ (q7 ◇ q6)) q5)).trans (rfl))).symm
  have apc9 : forall (q9 q10 q11 q12 q13 : G), (q13 ◇ ((q12 ◇ ((q10 ◇ q11) ◇ q12)) ◇ q13)) = (((q9 ◇ (q10 ◇ q9)) ◇ (q10 ◇ q11)) ◇ q11) := by
    intro q9 q10 q11 q12 q13
    exact (((rfl).symm).trans ((((congrArg (fun t => t ◇ q11) (congrArg (fun t => t ◇ (q10 ◇ q11)) (apc4 q9 q11 q10 q9))).symm).trans ((apc6 q11 q12 (q10 ◇ q11) q13).symm)).trans (rfl))).symm
  have apc49 : forall (q14 q15 : G), ((q15 ◇ (((q14 ◇ q14) ◇ q14) ◇ q15)) ◇ (q14 ◇ ((q14 ◇ q14) ◇ q14))) = (q14 ◇ (q14 ◇ q14)) := by
    intro q14 q15
    exact ((rfl).symm).trans ((((congrArg (fun t => (q15 ◇ (((q14 ◇ q14) ◇ q14) ◇ q15)) ◇ t) (congrArg (fun t => t ◇ ((q14 ◇ q14) ◇ q14)) (apc2 q14))).symm).trans ((h (q14 ◇ (q14 ◇ q14)) q15 ((q14 ◇ q14) ◇ q14)).symm)).trans (rfl))
  have apc50 : forall (q16 q17 : G), (q17 ◇ (q17 ◇ q17)) = (q16 ◇ (q17 ◇ q16)) := by
    intro q16 q17
    exact ((rfl).symm).trans ((((apc49 q17 q16).symm).trans (apc3 q17 q16 q17 q16)).trans (rfl))
  have apc53 : forall (q18 q19 q20 q21 : G), (q21 ◇ ((q20 ◇ ((q18 ◇ q19) ◇ q20)) ◇ q21)) = (((q18 ◇ (q18 ◇ q18)) ◇ (q18 ◇ q19)) ◇ q19) := by
    intro q18 q19 q20 q21
    exact (((rfl).symm).trans ((((congrArg (fun t => t ◇ q19) (congrArg (fun t => t ◇ (q18 ◇ q19)) ((apc50 q18 q18).symm))).symm).trans ((apc9 q18 q18 q19 q20 q21).symm)).trans (rfl))).symm
  have apc58 : forall (q22 q23 q24 q25 q26 : G), ((q26 ◇ ((q22 ◇ ((q22 ◇ q24) ◇ q24)) ◇ q26)) ◇ ((q23 ◇ (q24 ◇ q23)) ◇ (q22 ◇ ((q22 ◇ q24) ◇ q24)))) = (q25 ◇ (((q22 ◇ q24) ◇ q24) ◇ q25)) := by
    intro q22 q23 q24 q25 q26
    exact ((rfl).symm).trans ((((congrArg (fun t => (q26 ◇ ((q22 ◇ ((q22 ◇ q24) ◇ q24)) ◇ q26)) ◇ t) (congrArg (fun t => t ◇ (q22 ◇ ((q22 ◇ q24) ◇ q24))) (apc3 q22 q23 q24 q25))).symm).trans ((h (q25 ◇ (((q22 ◇ q24) ◇ q24) ◇ q25)) q26 (q22 ◇ ((q22 ◇ q24) ◇ q24))).symm)).trans (rfl))
  have apc59 : forall (q27 q28 : G), (q28 ◇ (((q27 ◇ q27) ◇ q27) ◇ q28)) = ((q27 ◇ q27) ◇ q27) := by
    intro q27 q28
    exact ((rfl).symm).trans ((((apc58 q27 ((q27 ◇ q27) ◇ q27) q27 q28 q27).symm).trans ((h ((q27 ◇ q27) ◇ q27) q27 (q27 ◇ ((q27 ◇ q27) ◇ q27))).symm)).trans (rfl))
  have apc60 : forall (q29 q30 : G), (((q29 ◇ q29) ◇ q29) ◇ ((q30 ◇ ((q29 ◇ q29) ◇ q29)) ◇ ((q29 ◇ q29) ◇ q29))) = q30 := by
    intro q29 q30
    exact ((rfl).symm).trans ((((congrArg (fun t => t ◇ ((q30 ◇ ((q29 ◇ q29) ◇ q29)) ◇ ((q29 ◇ q29) ◇ q29))) (apc59 q29 q29)).symm).trans ((h q30 q29 ((q29 ◇ q29) ◇ q29)).symm)).trans (rfl))
  have apc97 : forall (q31 : G), (((q31 ◇ (q31 ◇ q31)) ◇ (q31 ◇ q31)) ◇ q31) = q31 := by
    intro q31
    exact (((rfl).symm).trans ((((apc60 q31 q31).symm).trans (apc53 q31 q31 q31 ((q31 ◇ q31) ◇ q31))).trans (rfl))).symm
  exact (calc
    x = x := rfl
    _ = (y ◇ ((z ◇ ((x ◇ x) ◇ z)) ◇ y)) := ((apc53 x x z y).trans (apc97 x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22827_to_13979 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22827_to_13979
