-- Equation38968 → Equation55208
-- Recorded verdict: true
-- Premise: x = (((x * y) * (x * y)) * z) * z
-- Conclusion: x * (y * z) = x * ((y * x) * z)
-- Original submission SHA-256: 9c947b9ebca24e6df95c5ff9bc8b6e8d5ee0f75f5891ae63c9e925600c57d6cd
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((x ◇ y) ◇ (x ◇ y)) ◇ z) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = x ◇ ((y ◇ x) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), (q0 ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1))) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1))) ((h q0 q1 ((q0 ◇ q1) ◇ (q0 ◇ q1))).symm)).symm).trans ((h (q0 ◇ q1) (q0 ◇ q1) ((q0 ◇ q1) ◇ (q0 ◇ q1))).symm)
  have apc1 : forall (x y z:G), ((((x ◇ y) ◇ (x ◇ y)) ◇ z) ◇ z) = ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc2 : forall (q2:G), ((((q2 ◇ q2) ◇ (q2 ◇ q2)) ◇ q2) ◇ q2) = q2:=by
    intro q2
    exact ((apc1 q2 q2 q2).symm).trans ((h q2 q2 q2).symm)
  have apc3 : forall (q3:G), ((((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ q3) ◇ (q3 ◇ q3)) = q3:=by
    intro q3
    exact ((congrArg (fun t => (((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ q3) ◇ t) (congrArg (fun t => q3 ◇ t) (apc2 q3))).symm).trans ((((congrArg (fun t => (((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ q3) ◇ t) (congrArg (fun t => t ◇ ((((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ q3) ◇ q3)) (apc2 q3))).symm).trans (apc0 (((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ q3) q3)).trans (apc2 q3))
  have apc4 : forall (q0 q1 q4 q5:G), (((q0 ◇ ((((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ q4) ◇ q4)) ◇ q5) ◇ q5) = (((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ q4):=by
    intro q0 q1 q4 q5
    exact ((congrArg (fun t => t ◇ q5) (congrArg (fun t => t ◇ q5) (congrArg (fun t => t ◇ ((((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ q4) ◇ q4)) ((h q0 q1 q4).symm)))).symm).trans ((h (((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ q4) q4 q5).symm)
  have apc5 : forall (q6 q7 q8 q9:G), (((q6 ◇ q7) ◇ (q6 ◇ q7)) ◇ q8) = (((q6 ◇ q6) ◇ q9) ◇ q9):=by
    intro q6 q7 q8 q9
    exact (((congrArg (fun t => t ◇ q9) (congrArg (fun t => t ◇ q9) (congrArg (fun t => q6 ◇ t) ((h q6 q7 q8).symm)))).symm).trans (apc4 q6 q7 q8 q9)).symm
  have apc6 : forall (q10 q11 q12:G), ((q10 ◇ q11) ◇ (((q10 ◇ q10) ◇ q12) ◇ q12)) = ((q10 ◇ q11) ◇ (q10 ◇ q11)):=by
    intro q10 q11 q12
    exact ((congrArg (fun t => (q10 ◇ q11) ◇ t) (apc5 q10 q11 ((q10 ◇ q11) ◇ (q10 ◇ q11)) q12)).symm).trans (apc0 (q10 ◇ q11) (q10 ◇ q11))
  have apc7 : forall (q13 q14:G), ((((q14 ◇ q14) ◇ q13) ◇ q13) ◇ (q14 ◇ q14)) = q14:=by
    intro q13 q14
    exact ((congrArg (fun t => t ◇ (q14 ◇ q14)) (apc5 q14 q14 q14 q13)).symm).trans (apc3 q14)
  have apc8 : forall (q15 q16 q17:G), (((q15 ◇ q16) ◇ q17) ◇ ((q15 ◇ q16) ◇ q17)) = (((q15 ◇ q16) ◇ q17) ◇ q15):=by
    intro q15 q16 q17
    exact (((congrArg (fun t => ((q15 ◇ q16) ◇ q17) ◇ t) ((h q15 q16 q15).symm)).symm).trans (apc6 (q15 ◇ q16) q17 q15)).symm
  have apc11 : forall (q18 q19 q20:G), (q18 ◇ ((((q18 ◇ q19) ◇ (q18 ◇ q19)) ◇ q20) ◇ q20)) = (q18 ◇ q19):=by
    intro q18 q19 q20
    exact (((congrArg (fun t => t ◇ ((((q18 ◇ q19) ◇ (q18 ◇ q19)) ◇ q20) ◇ q20)) ((h q18 q19 q20).symm)).symm).trans (apc8 ((q18 ◇ q19) ◇ (q18 ◇ q19)) q20 q20)).trans (apc7 q20 (q18 ◇ q19))
  have apc12 : forall (q21 q22:G), (q21 ◇ q22) = (q21 ◇ q21):=by
    intro q21 q22
    exact (((congrArg (fun t => q21 ◇ t) ((h q21 q22 q21).symm)).symm).trans (apc11 q21 q22 q21)).symm
  exact (apc12 x (y ◇ z)).trans ((apc12 x ((y ◇ x) ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_38968_to_55208 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_38968_to_55208
