-- Equation46418 → Equation42029
-- Recorded verdict: true
-- Premise: x * y = (y * z) * (w * (u * v))
-- Conclusion: x * y = y * (z * (w * (u * y)))
-- Original submission SHA-256: cd34a04da9fa8c3fe0d25fc84cb72f3132b3428e1a741e33191ef0442008adc8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = (y ◇ z) ◇ (w ◇ (u ◇ v))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = y ◇ (z ◇ (w ◇ (u ◇ y)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z w u v:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w u v
    exact ((h x y z w u v).trans ((h y y z w u v).symm)).symm
  have apc1 : forall (q0 q1 q2 q3 q4:G), (q0 ◇ (q3 ◇ (q1 ◇ q2))) = (q4 ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((apc0 q0 (q3 ◇ (q1 ◇ q2)) q0 q0 q0 q0).symm).trans ((h q4 q3 (q1 ◇ q2) q3 q1 q2).symm)
  have apc2 : forall (q5 q6 q7 q8:G), (q5 ◇ (q7 ◇ (q6 ◇ q6))) = (q8 ◇ q7):=by
    intro q5 q6 q7 q8
    exact ((congrArg (fun t => q5 ◇ t) (congrArg (fun t => q7 ◇ t) ((apc0 q5 q6 q5 q5 q5 q5).symm))).symm).trans (apc1 q5 q5 q6 q7 q8)
  have apc3 : forall (q9 q10 q11 q12 q13 q14:G), (q12 ◇ (q11 ◇ (q9 ◇ q10))) = (q14 ◇ q13):=by
    intro q9 q10 q11 q12 q13 q14
    exact ((congrArg (fun t => q12 ◇ t) (apc1 q13 q9 q10 (q9 ◇ q10) q11)).symm).trans (apc2 q12 (q9 ◇ q10) q13 q14)
  have apc4 : forall (q15 q16 q17 q18 q19 q20 q21:G), (q19 ◇ (q18 ◇ (q17 ◇ (q15 ◇ q16)))) = (q21 ◇ q20):=by
    intro q15 q16 q17 q18 q19 q20 q21
    exact ((congrArg (fun t => q19 ◇ t) ((apc3 q15 q16 q17 q18 (q15 ◇ q15) q20).symm)).symm).trans (apc1 q19 q15 q15 q20 q21)
  have apc7 : forall (q22 q23 q24 q25 q26 q27:G), (q26 ◇ (q25 ◇ (q24 ◇ (q22 ◇ q23)))) = (q27 ◇ q27):=by
    intro q22 q23 q24 q25 q26 q27
    exact (apc4 q22 q23 q24 q25 q26 q27 q22).trans ((apc0 q22 q27 q22 q22 q22 q22).symm)
  have apc13 : forall (q28 q29 q30 q31:G), (q29 ◇ (q28 ◇ q28)) = (q31 ◇ q30):=by
    intro q28 q29 q30 q31
    exact ((congrArg (fun t => q29 ◇ t) (apc7 q28 q28 q28 q28 q28 q28)).symm).trans (apc4 q28 (q28 ◇ q28) q28 q28 q29 q30 q31)
  exact ((apc13 (x ◇ y) (y ◇ (z ◇ (w ◇ (u ◇ y)))) y x).symm).trans (apc13 (x ◇ y) (y ◇ (z ◇ (w ◇ (u ◇ y)))) (z ◇ (w ◇ (u ◇ y))) y)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46418_to_42029 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46418_to_42029
