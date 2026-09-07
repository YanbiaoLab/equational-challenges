-- Equation46528 → Equation42521
-- Recorded verdict: true
-- Premise: x * y = (z * y) * (y * (w * w))
-- Conclusion: x * x = y * (y * ((z * y) * z))
-- Original submission SHA-256: 386b025d1a46fdfce29d653d55e0aeac10f6b56f8a32ad59f7606aac402bcf2c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ y) ◇ (y ◇ (w ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (y ◇ ((z ◇ y) ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc2 : forall (q3 q4 q5 q6:G), (q3 ◇ (q6 ◇ (q4 ◇ q4))) = (q5 ◇ q6):=by
    intro q3 q4 q5 q6
    exact ((apc1 q3 (q3 ◇ q6) (q6 ◇ (q4 ◇ q4))).symm).trans ((h q5 q6 q3 q4).symm)
  have apc3 : forall (q7 q8 q9:G), (q7 ◇ (q9 ◇ (q8 ◇ q8))) = (q9 ◇ q9):=by
    intro q7 q8 q9
    exact (apc2 q7 q8 q7 q9).trans ((apc0 q7 q9 q7 q7).symm)
  have apc4 : forall (q10 q11 q12 q13:G), (q11 ◇ (q13 ◇ (q10 ◇ q12))) = (q13 ◇ q13):=by
    intro q10 q11 q12 q13
    exact ((congrArg (fun t => q11 ◇ t) (congrArg (fun t => q13 ◇ t) (apc0 q10 q12 q10 q10))).symm).trans (apc3 q11 q12 q13)
  have apc5 : forall (q14 q15 q16 q17:G), (q15 ◇ (q14 ◇ q14)) = (q16 ◇ q16):=by
    intro q14 q15 q16 q17
    exact ((congrArg (fun t => q15 ◇ t) (apc4 q17 q16 q17 q14)).symm).trans (((congrArg (fun t => q15 ◇ t) (congrArg (fun t => q16 ◇ t) ((h q14 (q17 ◇ q17) (q17 ◇ q17) q17).symm))).symm).trans (apc3 q15 ((q17 ◇ q17) ◇ (q17 ◇ q17)) q16))
  have apc7 : forall (q18 q19 q20 q21:G), (q19 ◇ (q18 ◇ q18)) = (q20 ◇ q21):=by
    intro q18 q19 q20 q21
    exact (apc5 q18 q19 q21 q18).trans (apc0 q20 q21 q18 q18)
  exact ((apc7 (x ◇ x) (y ◇ (y ◇ ((z ◇ y) ◇ z))) x x).symm).trans (apc7 (x ◇ x) (y ◇ (y ◇ ((z ◇ y) ◇ z))) y (y ◇ ((z ◇ y) ◇ z)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46528_to_42521 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46528_to_42521
