-- Equation55535 → Equation55123
-- Recorded verdict: true
-- Premise: x * (y * z) = w * ((u * y) * v)
-- Conclusion: x * (y * y) = z * ((x * z) * w)
-- Original submission SHA-256: bb1f7b0b190ed19fe24a1f13aa105db9db0c140bb56f0f3b8d60f0037eb23043
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ (y ◇ z) = w ◇ ((u ◇ y) ◇ v)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = z ◇ ((x ◇ z) ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u v:G), (y ◇ (y ◇ y)) = (x ◇ (y ◇ z)):=by
    intro x y z w u v
    exact ((h x y z w u v).trans ((h y y y w u v).symm)).symm
  have apc1 : forall (q0 q1 q2 q3:G), (q2 ◇ ((q0 ◇ q3) ◇ q1)) = (q3 ◇ (q3 ◇ q3)):=by
    intro q0 q1 q2 q3
    exact ((apc0 q0 q3 q0 q0 q0 q0).trans (h q0 q3 q0 q2 q0 q1)).symm
  have apc2 : forall (q4 q5 q6 q7 q8:G), (q6 ◇ (q7 ◇ q8)) = (q4 ◇ (q7 ◇ q5)):=by
    intro q4 q5 q6 q7 q8
    exact ((h q4 q7 q5 q4 q4 q4).trans ((h q6 q7 q8 q4 q4 q4).symm)).symm
  have apc3 : forall (q4 q5 q6 q7 q8:G), (q6 ◇ (q7 ◇ q6)) = (q4 ◇ (q7 ◇ q5)):=by
    intro q4 q5 q6 q7 q8
    exact (((apc2 q4 q5 q6 q7 q8).symm).trans (apc2 q6 q6 q6 q7 q8)).symm
  have apc6 : forall (q9 q4 q10 q5 q11 q12 q13:G), (q13 ◇ ((q11 ◇ (q9 ◇ q10)) ◇ q12)) = (q4 ◇ (q10 ◇ q5)):=by
    intro q9 q4 q10 q5 q11 q12 q13
    exact ((h q4 q10 q5 q9 q9 q9).trans (h q9 (q9 ◇ q10) q9 q13 q11 q12)).symm
  have apc7 : forall (q14 q15 q16 q17 q18 q19 q20 q21 q22:G), (q19 ◇ ((q14 ◇ (q14 ◇ q14)) ◇ q18)) = (q15 ◇ (q16 ◇ q17)):=by
    intro q14 q15 q16 q17 q18 q19 q20 q21 q22
    exact ((congrArg (fun t => q19 ◇ t) (congrArg (fun t => t ◇ q18) (apc1 q20 q21 q22 q14))).symm).trans (((congrArg (fun t => q19 ◇ t) (congrArg (fun t => t ◇ q18) (h q20 q14 q16 q22 q20 q21))).symm).trans (apc6 q14 q15 q16 q17 q20 q18 q19))
  have apc8 : forall (q23 q24 q25 q26 q27 q28:G), (q26 ◇ (q27 ◇ q28)) = (q23 ◇ (q24 ◇ q25)):=by
    intro q23 q24 q25 q26 q27 q28
    exact (((apc7 q23 q23 q24 q25 q23 q23 q23 q23 q23).symm).trans (apc7 q23 q26 q27 q28 q23 q23 q23 q23 q23)).symm
  have apc9 : forall (q29 q30 q31 q32 q33:G), (q32 ◇ (q33 ◇ q32)) = (q29 ◇ (q30 ◇ q31)):=by
    intro q29 q30 q31 q32 q33
    exact (((apc8 q29 q30 q31 q29 q33 q29).symm).trans ((apc3 q29 q29 q32 q33 q29).symm)).symm
  exact ((apc9 x y y (x ◇ (y ◇ y)) (z ◇ ((x ◇ z) ◇ w))).symm).trans (apc9 z (x ◇ z) w (x ◇ (y ◇ y)) (z ◇ ((x ◇ z) ◇ w)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_55535_to_55123 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_55535_to_55123
