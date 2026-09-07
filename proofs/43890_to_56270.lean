-- Equation43890 → Equation56270
-- Recorded verdict: true
-- Premise: x * y = z * ((y * y) * (z * x))
-- Conclusion: x * (y * z) = (z * z) * (w * u)
-- Original submission SHA-256: eeb905d315a284280f41348300dcb3bb2f850aeacabe6bdca138a8bd37f6e7b0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ ((y ◇ y) ◇ (z ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = (z ◇ z) ◇ (w ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2:G), (((q2 ◇ q2) ◇ q0) ◇ q2) = ((q1 ◇ q1) ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => (q1 ◇ q1) ◇ t) ((h q0 q1 (q2 ◇ q2)).symm)).symm).trans ((h ((q2 ◇ q2) ◇ q0) q2 (q1 ◇ q1)).symm)).symm
  have apc1 : forall (q3 q4 q5:G), ((q5 ◇ q5) ◇ (q4 ◇ q5)) = ((q3 ◇ q3) ◇ (q4 ◇ q3)):=by
    intro q3 q4 q5
    exact (((apc0 q4 q3 q3).symm).trans (apc0 q4 q5 q3)).symm
  have apc2 : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ (q0 ◇ q1)) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact ((apc0 q0 q1 q2).symm).trans (apc0 q0 q0 q2)
  have apc4 : forall (x y z:G), (z ◇ ((y ◇ y) ◇ (z ◇ x))) = (x ◇ ((y ◇ y) ◇ (x ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc8 : forall (q6 q7 q8 q9:G), (((q6 ◇ q6) ◇ (q7 ◇ q6)) ◇ (q9 ◇ (q7 ◇ q7))) = ((q8 ◇ q8) ◇ (q9 ◇ q8)):=by
    intro q6 q7 q8 q9
    exact ((congrArg (fun t => t ◇ (q9 ◇ (q7 ◇ q7))) (apc1 q6 q7 q7)).symm).trans (apc1 q8 q9 (q7 ◇ q7))
  have apc9 : forall (q10 q11 q12:G), (q11 ◇ ((q11 ◇ q11) ◇ (q11 ◇ q11))) = ((q10 ◇ q10) ◇ (q10 ◇ q10)):=by
    intro q10 q11 q12
    exact ((apc4 q11 q11 q12).symm).trans (((congrArg (fun t => q12 ◇ t) (apc8 q10 q10 q11 q12)).symm).trans ((h (q10 ◇ q10) (q10 ◇ q10) q12).symm))
  have apc11 : forall (q13 q14:G), ((q13 ◇ q13) ◇ (q13 ◇ q13)) = (q14 ◇ q14):=by
    intro q13 q14
    exact ((apc9 q13 q14 q13).symm).trans ((h q14 q14 q14).symm)
  have apc18 : forall (q15 q16:G), (q16 ◇ (q15 ◇ q15)) = (q16 ◇ q16):=by
    intro q15 q16
    exact ((congrArg (fun t => q16 ◇ t) (apc11 q16 q15)).symm).trans ((h q16 q16 q16).symm)
  have apc20 : forall (q17 q5 q18 q3:G), (((q18 ◇ q18) ◇ ((q5 ◇ q5) ◇ q17)) ◇ q18) = ((q5 ◇ q5) ◇ (q5 ◇ q5)):=by
    intro q17 q5 q18 q3
    exact ((((congrArg (fun t => (q5 ◇ q5) ◇ t) (apc2 q17 q3 ((q3 ◇ q3) ◇ (q17 ◇ q3)))).trans (apc18 (q17 ◇ q17) (q5 ◇ q5))).symm).trans (((congrArg (fun t => (q5 ◇ q5) ◇ t) (apc0 q17 q3 q5)).symm).trans ((apc0 ((q5 ◇ q5) ◇ q17) q5 q18).symm))).symm
  have apc21 : forall (q19 q20 q21:G), ((q20 ◇ q20) ◇ (q20 ◇ q20)) = ((q19 ◇ q20) ◇ q21):=by
    intro q19 q20 q21
    exact (((congrArg (fun t => t ◇ q21) ((h q19 q20 (q21 ◇ q21)).symm)).symm).trans (apc20 ((q21 ◇ q21) ◇ q19) q20 q21 q19)).symm
  have apc22 : forall (q22 q23 q24:G), ((q22 ◇ q22) ◇ (q22 ◇ q22)) = (q23 ◇ q24):=by
    intro q22 q23 q24
    exact (apc21 q22 q22 ((q24 ◇ q24) ◇ ((q22 ◇ q22) ◇ q23))).trans ((h q23 q24 (q22 ◇ q22)).symm)
  exact ((apc22 (x ◇ (y ◇ z)) x (y ◇ z)).symm).trans (apc22 (x ◇ (y ◇ z)) (z ◇ z) (w ◇ u))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43890_to_56270 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43890_to_56270
