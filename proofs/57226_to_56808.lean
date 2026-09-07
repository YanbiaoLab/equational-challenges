-- Equation57226 → Equation56808
-- Recorded verdict: true
-- Premise: x * (y * z) = (w * (z * x)) * x
-- Conclusion: x * (y * y) = (x * (y * z)) * x
-- Original submission SHA-256: 20e19fb72b577c35364339305e65146e7eb9ecbdca71174ef3e063cc5b6e2731
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (w ◇ (z ◇ x)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ y) = (x ◇ (y ◇ z)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (x ◇ (y ◇ z)) = (x ◇ (x ◇ z)):=by
    intro x y z w
    exact (h x y z x).trans ((h x x z x).symm)
  have apc1 : forall (x y z w:G), ((x ◇ (x ◇ x)) ◇ x) = ((w ◇ (w ◇ x)) ◇ x):=by
    intro x y z w
    exact (((congrArg (fun t => t ◇ x) (apc0 w z x (w ◇ (z ◇ x)))).symm).trans ((((h x x z w).symm).trans (h x x z x)).trans (congrArg (fun t => t ◇ x) (apc0 x z x (x ◇ (z ◇ x)))))).symm
  have apc4 : forall (x y z w:G), ((w ◇ (w ◇ x)) ◇ x) = (x ◇ (x ◇ z)):=by
    intro x y z w
    exact (((apc0 x x z (x ◇ (x ◇ z))).symm).trans ((h x x z w).trans (congrArg (fun t => t ◇ x) (apc0 w z x (w ◇ (z ◇ x)))))).symm
  have apc5 : forall (x y z w:G), (x ◇ (x ◇ z)) = (x ◇ (x ◇ x)):=by
    intro x y z w
    exact ((apc4 x x z x).symm).trans (apc4 x x x x)
  have apc6 : forall (q0 q1 q2 q3:G), (q1 ◇ (q2 ◇ q3)) = (q1 ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2 q3
    exact (((apc4 q1 q0 q0 q3).symm).trans ((h q1 q2 q3 q3).symm)).symm
  have apc14 : forall (q4 q5 q6 q7:G), (q6 ◇ (q7 ◇ (q4 ◇ q5))) = (q6 ◇ (q6 ◇ q6)):=by
    intro q4 q5 q6 q7
    exact (((congrArg (fun t => q6 ◇ t) ((h q7 q4 q5 q4).symm)).symm).trans (apc0 q6 (q4 ◇ (q5 ◇ q7)) q7 q4)).trans (apc5 q6 (q6 ◇ (q6 ◇ q7)) q7 (q6 ◇ (q6 ◇ q7)))
  have apc23 : forall (q8 q9 q10 q11:G), ((q10 ◇ ((q8 ◇ q9) ◇ q11)) ◇ q11) = (q11 ◇ (q11 ◇ q11)):=by
    intro q8 q9 q10 q11
    exact (((apc14 q8 q9 q11 q8).symm).trans (((congrArg (fun t => q11 ◇ t) (apc0 q8 q8 q9 q8)).symm).trans (h q11 q8 (q8 ◇ q9) q10))).symm
  have apc24 : forall (q12 q13 q14:G), ((q13 ◇ (q13 ◇ q13)) ◇ q14) = ((q12 ◇ (q12 ◇ q12)) ◇ q14):=by
    intro q12 q13 q14
    exact (((congrArg (fun t => t ◇ q14) (apc5 q12 (q12 ◇ (q12 ◇ q14)) q14 (q12 ◇ (q12 ◇ q14)))).symm).trans ((((apc1 q14 q12 q12 q12).symm).trans (apc1 q14 q12 q12 q13)).trans (congrArg (fun t => t ◇ q14) (apc5 q13 (q13 ◇ (q13 ◇ q14)) q14 (q13 ◇ (q13 ◇ q14)))))).symm
  have apc35 : forall (q15 q16 q17:G), ((q16 ◇ (q16 ◇ q15)) ◇ q17) = (q17 ◇ (q17 ◇ q17)):=by
    intro q15 q16 q17
    exact ((congrArg (fun t => t ◇ q17) (apc6 q15 q16 (q15 ◇ q15) q17)).symm).trans (apc23 q15 q15 q16 q17)
  have apc36 : forall (q18 q19 q20 q21:G), ((q20 ◇ (q18 ◇ q19)) ◇ q21) = (q21 ◇ (q21 ◇ q21)):=by
    intro q18 q19 q20 q21
    exact (((congrArg (fun t => t ◇ q21) ((apc6 q20 q20 q18 q19).symm)).symm).trans (apc24 q18 q20 q21)).trans (apc35 q18 q18 q21)
  exact (calc
    (x ◇ (y ◇ y)) = (x ◇ (x ◇ x)):=apc6 x x y y
    _ = ((x ◇ (y ◇ z)) ◇ x):=(apc36 y z x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_57226_to_56808 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_57226_to_56808
