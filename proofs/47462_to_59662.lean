-- Equation47462 → Equation59662
-- Recorded verdict: true
-- Premise: x * y = (z * z) * ((x * w) * x)
-- Conclusion: (x * y) * z = y * ((x * z) * w)
-- Original submission SHA-256: 7d234f236e26c578c6c9e587d05d1e8945d91e24a82ef41c83f9fa0b5a0c090b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ z) ◇ ((x ◇ w) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = y ◇ ((x ◇ z) ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y x x).trans ((h x x x x).symm)
  have apc1 : forall (x y z w:G), ((z ◇ z) ◇ (z ◇ z)) = (x ◇ x):=by
    intro x y z w
    exact (((apc0 x x (x ◇ x) (x ◇ x)).symm).trans ((h x x z x).trans (apc0 (z ◇ z) ((x ◇ x) ◇ x) ((z ◇ z) ◇ ((x ◇ x) ◇ x)) ((z ◇ z) ◇ ((x ◇ x) ◇ x))))).symm
  have apc2 : forall (x y z w:G), (z ◇ z) = (x ◇ x):=by
    intro x y z w
    exact (((apc1 x x z x).symm).trans (apc1 z x z x)).symm
  have apc3 : forall (q0 q1 q2 q3:G), (((q1 ◇ q0) ◇ q1) ◇ q2) = ((q3 ◇ q3) ◇ (q1 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => (q3 ◇ q3) ◇ t) (apc0 q1 q0 (q1 ◇ q0) (q1 ◇ q0))).symm).trans (((congrArg (fun t => (q3 ◇ q3) ◇ t) ((h q1 q0 ((q1 ◇ q0) ◇ q1) q0).symm)).symm).trans ((h ((q1 ◇ q0) ◇ q1) q2 q3 ((q1 ◇ q0) ◇ q1)).symm))).symm
  have apc4 : forall (q4 q5 q6 q7:G), ((q7 ◇ q7) ◇ (q7 ◇ q7)) = ((q5 ◇ q4) ◇ q6):=by
    intro q4 q5 q6 q7
    exact (((congrArg (fun t => (q7 ◇ q7) ◇ t) (apc0 (q4 ◇ q4) (q5 ◇ q5) ((q4 ◇ q4) ◇ (q5 ◇ q5)) ((q4 ◇ q4) ◇ (q5 ◇ q5)))).trans (apc0 (q7 ◇ q7) ((q4 ◇ q4) ◇ (q4 ◇ q4)) ((q7 ◇ q7) ◇ ((q4 ◇ q4) ◇ (q4 ◇ q4))) ((q7 ◇ q7) ◇ ((q4 ◇ q4) ◇ (q4 ◇ q4))))).symm).trans (((congrArg (fun t => (q7 ◇ q7) ◇ t) (apc3 q4 q5 (q5 ◇ q4) q4)).symm).trans ((h (q5 ◇ q4) q6 q7 q5).symm))
  have apc5 : forall (q4 q5 q6 q7:G), ((q7 ◇ q7) ◇ q7) = ((q5 ◇ q4) ◇ q6):=by
    intro q4 q5 q6 q7
    exact (((apc4 q4 q5 q6 q7).symm).trans (apc4 q7 q7 q7 q7)).symm
  have apc7 : forall (q8 q9 q10 q11:G), ((q9 ◇ q8) ◇ q10) = (q11 ◇ q11):=by
    intro q8 q9 q10 q11
    exact ((apc4 q8 q9 q10 q8).symm).trans (apc2 q11 q8 (q8 ◇ q8) q8)
  have apc8 : forall (q12 q13:G), ((q12 ◇ q12) ◇ q12) = (q13 ◇ q13):=by
    intro q12 q13
    exact (apc5 q12 q12 (q12 ◇ q12) q12).trans (apc2 q13 q12 (q12 ◇ q12) q12)
  have apc48 : forall (q14 q15 q16 q17:G), ((q16 ◇ q16) ◇ (q15 ◇ q14)) = (q17 ◇ q17):=by
    intro q14 q15 q16 q17
    exact ((congrArg (fun t => t ◇ (q15 ◇ q14)) (apc7 q14 q15 (q15 ◇ q14) q16)).symm).trans (apc8 (q15 ◇ q14) q17)
  have apc49 : forall (q18 q19 q20:G), (q20 ◇ q20) = (q19 ◇ q18):=by
    intro q18 q19 q20
    exact ((h q19 q18 q18 q18).trans (apc48 q19 (q19 ◇ q18) q18 q20)).symm
  exact ((apc49 z (x ◇ y) ((x ◇ y) ◇ z)).symm).trans (apc49 ((x ◇ z) ◇ w) y ((x ◇ y) ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47462_to_59662 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47462_to_59662
