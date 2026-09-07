-- Equation47397 → Equation61211
-- Recorded verdict: true
-- Premise: x * y = (z * y) * ((y * y) * w)
-- Conclusion: (x * y) * y = (x * (z * w)) * z
-- Original submission SHA-256: 8df21ba64b01cbbb4429a26cc48de7ea50c0c79c0da4a472c8c0d0c6eda96be2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ y) ◇ ((y ◇ y) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ y = (x ◇ (z ◇ w)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc2 : forall (q0 q1 q2 q3:G), ((q3 ◇ q2) ◇ (q0 ◇ q2)) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => (q3 ◇ q2) ◇ t) ((h q0 q2 q2 q0).symm)).symm).trans ((h q1 q2 q3 ((q2 ◇ q2) ◇ q0)).symm)
  have apc3 : forall (q4 q5 q6 q7:G), ((q7 ◇ q6) ◇ (q4 ◇ q4)) = (q5 ◇ q6):=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => (q7 ◇ q6) ◇ t) ((apc0 (q6 ◇ q6) q4 q4 q4).symm)).symm).trans ((h q5 q6 q7 q4).symm)
  have apc4 : forall (q8 q9 q10 q11 q12:G), ((q9 ◇ (q10 ◇ q12)) ◇ (q8 ◇ q8)) = (q11 ◇ q12):=by
    intro q8 q9 q10 q11 q12
    exact (apc3 q8 (q8 ◇ q12) (q10 ◇ q12) q9).trans (apc2 q10 q11 q12 q8)
  have apc7 : forall (q13 q14 q15 q16 q17:G), ((q17 ◇ (q13 ◇ q13)) ◇ (q16 ◇ q16)) = (q14 ◇ q15):=by
    intro q13 q14 q15 q16 q17
    exact (((apc3 q13 q14 q15 q13).symm).trans ((apc3 q16 (q13 ◇ q15) (q13 ◇ q13) q17).symm)).symm
  have apc12 : forall (q18 q19 q20 q21:G), (q20 ◇ q21) = (q18 ◇ q19):=by
    intro q18 q19 q20 q21
    exact (((apc7 q21 q18 q19 q18 q18).symm).trans (apc4 q18 q18 q21 q20 q21)).symm
  exact (apc12 ((x ◇ y) ◇ y) ((x ◇ (z ◇ w)) ◇ z) (x ◇ y) y).trans ((apc12 ((x ◇ y) ◇ y) ((x ◇ (z ◇ w)) ◇ z) (x ◇ (z ◇ w)) z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47397_to_61211 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47397_to_61211
