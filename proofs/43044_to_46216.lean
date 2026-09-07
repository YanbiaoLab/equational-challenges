-- Equation43044 → Equation46216
-- Recorded verdict: true
-- Premise: x * y = z * (y * ((w * y) * x))
-- Conclusion: x * y = (x * z) * (y * (z * x))
-- Original submission SHA-256: e1aa38144fdb7a61db6c78ea4fe7ee48ef4b7778041efaa19c76ff9aa6ce24b3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (y ◇ ((w ◇ y) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (x ◇ z) ◇ (y ◇ (z ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), (((q0 ◇ (q2 ◇ q3)) ◇ q1) ◇ q3) = (q4 ◇ (q1 ◇ (q2 ◇ q3))):=by
    intro q0 q1 q2 q3 q4
    exact (((congrArg (fun t => q4 ◇ t) ((h q1 (q2 ◇ q3) q3 q0).symm)).symm).trans ((h ((q0 ◇ (q2 ◇ q3)) ◇ q1) q3 q4 q2).symm)).symm
  have apc1 : forall (q5 q6 q7 q8 q9:G), (q9 ◇ (q8 ◇ (q6 ◇ (q8 ◇ (q5 ◇ q7))))) = (q7 ◇ q8):=by
    intro q5 q6 q7 q8 q9
    exact ((congrArg (fun t => q9 ◇ t) (congrArg (fun t => q8 ◇ t) (apc0 q5 q8 q5 q7 q6))).symm).trans ((h q7 q8 q9 (q5 ◇ (q5 ◇ q7))).symm)
  have apc2 : forall (q10 q11 q12:G), (q12 ◇ (q11 ◇ (q10 ◇ q11))) = (q10 ◇ q11):=by
    intro q10 q11 q12
    exact ((congrArg (fun t => q12 ◇ t) (congrArg (fun t => q11 ◇ t) ((h q10 q11 q10 q10).symm))).symm).trans (apc1 (q10 ◇ q11) q10 q10 q11 q12)
  have apc3 : forall (q13 q14 q15 q16 q17 q18 q19:G), (q16 ◇ (q15 ◇ (q13 ◇ q14))) = (q13 ◇ q14):=by
    intro q13 q14 q15 q16 q17 q18 q19
    exact ((((apc1 q17 q18 q13 q14 ((q17 ◇ (q19 ◇ (q14 ◇ (q18 ◇ (q14 ◇ (q17 ◇ q13)))))) ◇ q15)).symm).trans (apc0 q17 q15 q19 (q14 ◇ (q18 ◇ (q14 ◇ (q17 ◇ q13)))) q16)).trans (congrArg (fun t => q16 ◇ t) (congrArg (fun t => q15 ◇ t) (apc1 q17 q18 q13 q14 q19)))).symm
  have apc4 : forall (q20 q21 q22:G), ((q20 ◇ q22) ◇ q21) = (q21 ◇ q22):=by
    intro q20 q21 q22
    exact ((apc3 (q20 ◇ q22) q21 q22 q20 q20 q20 q20).symm).trans ((h q21 q22 q20 q20).symm)
  have apc5 : forall (q23 q24 q25 q26:G), (q23 ◇ (q24 ◇ q25)) = (q24 ◇ q25):=by
    intro q23 q24 q25 q26
    exact ((apc4 q26 q23 (q24 ◇ q25)).symm).trans (((apc4 q23 (q26 ◇ (q24 ◇ q25)) q23).symm).trans (apc3 q24 q25 q26 (q23 ◇ q23) q23 q23 q23))
  have apc6 : forall (q27 q28 q29 q30:G), (q28 ◇ q29) = (q27 ◇ q28):=by
    intro q27 q28 q29 q30
    exact ((((congrArg (fun t => q30 ◇ t) (apc5 q29 q27 q28 (q29 ◇ (q27 ◇ q28)))).trans (apc5 q30 q27 q28 (q30 ◇ (q27 ◇ q28)))).symm).trans (((congrArg (fun t => q30 ◇ t) (apc2 q29 (q27 ◇ q28) q29)).symm).trans (apc1 q27 (q27 ◇ q28) q28 q29 q30))).symm
  exact (apc6 (y ◇ (z ◇ x)) x y (x ◇ y)).trans (apc6 (x ◇ z) (y ◇ (z ◇ x)) x (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43044_to_46216 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43044_to_46216
