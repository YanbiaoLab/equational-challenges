-- Equation47241 → Equation60542
-- Recorded verdict: true
-- Premise: x * y = (y * z) * ((y * y) * y)
-- Conclusion: (x * y) * z = (y * x) * (w * z)
-- Original submission SHA-256: 9f50c5d266114c5536a05ca2b9364bc15bc5b4694ce47c8b7b18ab408d9ecc07
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ z) ◇ ((y ◇ y) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = (y ◇ x) ◇ (w ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc3 : forall (x y z:G), (y ◇ y) = (x ◇ y):=by
    intro x y z
    exact ((h x y z).trans ((h y y z).symm)).symm
  have apc4 : forall (q0 q1 q2:G), ((q1 ◇ q2) ◇ (q1 ◇ q1)) = (q0 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q1 ◇ q2) ◇ t) ((apc3 (q1 ◇ q1) q1 q0).symm)).symm).trans ((h q0 q1 q2).symm)
  have apc5 : forall (q3 q4 q5:G), (q4 ◇ q5) = (q3 ◇ q5):=by
    intro q3 q4 q5
    exact ((h q3 q5 q3).trans ((h q4 q5 q3).symm)).symm
  have apc6 : forall (q6 q7 q8 q9:G), ((q8 ◇ q9) ◇ (q6 ◇ q8)) = (q7 ◇ q8):=by
    intro q6 q7 q8 q9
    exact ((congrArg (fun t => (q8 ◇ q9) ◇ t) (apc3 q6 q8 q6)).symm).trans (apc4 q7 q8 q9)
  have apc7 : forall (q10 q11 q12 q13 q14:G), ((q10 ◇ q14) ◇ (q11 ◇ q13)) = (q12 ◇ q13):=by
    intro q10 q11 q12 q13 q14
    exact ((congrArg (fun t => t ◇ (q11 ◇ q13)) (apc5 q10 q13 q14)).symm).trans (apc6 q11 q12 q13 q14)
  have apc9 : forall (q15 q16 q17 q18:G), ((q15 ◇ q17) ◇ (q16 ◇ q18)) = (q18 ◇ q18):=by
    intro q15 q16 q17 q18
    exact (apc7 q15 q16 q15 q18 q17).trans ((apc3 q15 q18 q15).symm)
  have apc10 : forall (q19 q20 q4 q3:G), (q4 ◇ (q19 ◇ q20)) = (q20 ◇ q20):=by
    intro q19 q20 q4 q3
    exact (((((congrArg (fun t => (q3 ◇ q19) ◇ t) (congrArg (fun t => t ◇ (q19 ◇ q20)) (apc9 q19 q19 q20 q20))).trans (congrArg (fun t => (q3 ◇ q19) ◇ t) (apc9 q20 q19 q20 q20))).trans (apc9 q3 q20 q19 q20)).symm).trans (((congrArg (fun t => t ◇ (((q19 ◇ q20) ◇ (q19 ◇ q20)) ◇ (q19 ◇ q20))) ((h q3 q19 q20).symm)).symm).trans ((h q4 (q19 ◇ q20) ((q19 ◇ q19) ◇ q19)).symm))).symm
  exact (calc
    ((x ◇ y) ◇ z) = (z ◇ z):=(apc3 (x ◇ y) z w).symm
    _ = ((y ◇ x) ◇ (w ◇ z)):=(apc10 w z (y ◇ x) w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47241_to_60542 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47241_to_60542
