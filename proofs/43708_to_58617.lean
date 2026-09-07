-- Equation43708 → Equation58617
-- Recorded verdict: true
-- Premise: x * y = y * ((y * z) * (w * z))
-- Conclusion: (x * y) * y = y * (z * (w * z))
-- Original submission SHA-256: 962cd1431d9f427318d25e6b3e24c2f176578e86bba02a909c810fb0bffee751
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ ((y ◇ z) ◇ (w ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ y = y ◇ (z ◇ (w ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc1 : forall (q0 q1 q2 q3:G), (q1 ◇ (q0 ◇ (q1 ◇ q3))) = (q2 ◇ q1):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q1 ◇ t) (apc0 q0 (q1 ◇ q3) q0 q0)).symm).trans ((h q2 q1 q3 q1).symm)
  have apc3 : forall (q4 q5 q6 q7:G), (q5 ◇ (q4 ◇ (q7 ◇ q7))) = (q6 ◇ q5):=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => q5 ◇ t) (congrArg (fun t => q4 ◇ t) ((apc0 q5 q7 q4 q4).symm))).symm).trans (apc1 q4 q5 q6 q7)
  have apc4 : forall (q8 q9 q10 q11 q12:G), (q10 ◇ (q9 ◇ (q8 ◇ q12))) = (q11 ◇ q10):=by
    intro q8 q9 q10 q11 q12
    exact ((congrArg (fun t => q10 ◇ t) (congrArg (fun t => q9 ◇ t) (apc0 q8 q12 q8 q8))).symm).trans (apc3 q9 q10 q11 q12)
  have apc7 : forall (q13 q14 q15:G), (q15 ◇ (q13 ◇ (q14 ◇ q14))) = (q15 ◇ q15):=by
    intro q13 q14 q15
    exact (apc3 q13 q15 q13 q14).trans ((apc0 q13 q15 q13 q13).symm)
  have apc11 : forall (q16 q17 q18:G), (q17 ◇ q18) = (q16 ◇ q18):=by
    intro q16 q17 q18
    exact ((h q16 q18 q16 q16).trans ((h q17 q18 q16 q16).symm)).symm
  have apc15 : forall (q19 q20 q21:G), (q21 ◇ (q19 ◇ q20)) = (q21 ◇ q21):=by
    intro q19 q20 q21
    exact ((congrArg (fun t => q21 ◇ t) (apc4 q19 (q19 ◇ q19) q20 q19 q19)).symm).trans (apc7 q20 (q19 ◇ q19) q21)
  have apc16 : forall (q22 q23 q24 q25 q26:G), (q23 ◇ q24) = (q22 ◇ q22):=by
    intro q22 q23 q24 q25 q26
    exact (((apc15 (q24 ◇ q25) (q26 ◇ q25) q22).symm).trans (((apc11 q22 q24 ((q24 ◇ q25) ◇ (q26 ◇ q25))).symm).trans ((h q23 q24 q25 q26).symm))).symm
  exact (apc16 ((x ◇ y) ◇ y) (x ◇ y) y ((x ◇ y) ◇ y) ((x ◇ y) ◇ y)).trans ((apc16 ((x ◇ y) ◇ y) y (z ◇ (w ◇ z)) ((x ◇ y) ◇ y) ((x ◇ y) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43708_to_58617 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43708_to_58617
