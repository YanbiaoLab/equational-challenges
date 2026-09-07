-- Equation51629 → Equation45722
-- Recorded verdict: true
-- Premise: x * y = ((y * z) * (y * z)) * x
-- Conclusion: x * y = z * (((z * y) * z) * y)
-- Original submission SHA-256: 58de68be7b03d95759856333438065c479bf8af6b43f0b06966d8766ab7fb542
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((y ◇ z) ◇ (y ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ (((z ◇ y) ◇ z) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ q0) ◇ q2) = (q2 ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q2) ((h ((q0 ◇ q1) ◇ (q0 ◇ q1)) q0 q1).symm)).symm).trans ((h q2 (q0 ◇ q1) (q0 ◇ q1)).symm)
  have apc1 : forall (q3 q4 q5:G), (q5 ◇ (q3 ◇ q4)) = ((q3 ◇ q3) ◇ q5):=by
    intro q3 q4 q5
    exact (((congrArg (fun t => t ◇ q5) ((h q3 q3 q4).symm)).symm).trans (apc0 q3 q4 q5)).symm
  have apc2 : forall (q6 q7 q8:G), (q8 ◇ ((q6 ◇ q6) ◇ q7)) = ((q7 ◇ q7) ◇ q8):=by
    intro q6 q7 q8
    exact ((congrArg (fun t => q8 ◇ t) (apc1 q6 q6 q7)).symm).trans (apc1 q7 (q6 ◇ q6) q8)
  have apc4 : forall (x y z:G), (((y ◇ y) ◇ (y ◇ y)) ◇ x) = (((y ◇ x) ◇ (y ◇ x)) ◇ x):=by
    intro x y z
    exact (((congrArg (fun t => t ◇ x) (apc1 y z (y ◇ z))).trans (congrArg (fun t => t ◇ x) (apc1 y z (y ◇ y)))).symm).trans (((h x y z).symm).trans (h x y x))
  have apc5 : forall (q9 q10:G), (((q10 ◇ q9) ◇ (q10 ◇ q9)) ◇ q9) = (q9 ◇ q10):=by
    intro q9 q10
    exact ((apc4 q9 q10 q9).symm).trans ((h q9 q10 q10).symm)
  have apc6 : forall (q11 q12:G), ((q11 ◇ q11) ◇ q12) = (q12 ◇ q12):=by
    intro q11 q12
    exact ((((congrArg (fun t => t ◇ q12) (apc2 q11 q12 (q12 ◇ q12))).trans (apc5 q12 q12)).symm).trans ((((congrArg (fun t => t ◇ q12) (apc2 q11 q12 ((q11 ◇ q11) ◇ q12))).symm).trans (apc5 q12 (q11 ◇ q11))).trans (apc1 q11 q11 q12))).symm
  have apc9 : forall (q11 q12 q9 q10:G), (q9 ◇ q10) = (q9 ◇ q9):=by
    intro q11 q12 q9 q10
    exact (((apc6 (q10 ◇ q9) q9).symm).trans (apc5 q9 q10)).symm
  have apc10 : forall (q13 q14:G), ((q13 ◇ q13) ◇ (q13 ◇ q13)) = (q14 ◇ q14):=by
    intro q13 q14
    exact ((apc9 q13 q13 (q13 ◇ q13) q14).symm).trans (apc6 q13 q14)
  have apc11 : forall (q13 q14:G), (q14 ◇ q14) = (q13 ◇ q13):=by
    intro q13 q14
    exact ((apc10 q13 q14).symm).trans (apc10 q13 q13)
  exact (calc
    (x ◇ y) = (x ◇ x):=apc9 x x x y
    _ = (z ◇ z):=apc11 z x
    _ = (z ◇ (((z ◇ y) ◇ z) ◇ y)):=(apc9 x x z (((z ◇ y) ◇ z) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51629_to_45722 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51629_to_45722
