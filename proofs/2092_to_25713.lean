-- Equation2092 → Equation25713
-- Recorded verdict: true
-- Premise: x = ((y ◇ x) ◇ x) ◇ (y ◇ z)
-- Conclusion: x = (y ◇ (z ◇ (w ◇ u))) ◇ (y ◇ y)
-- Original submission SHA-256: 921bfce32593c98ef3e20e9d711cc7098cc24b7fb88a1a8edece178ba6caa518
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ x) ◇ (y ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ (z ◇ (w ◇ u))) ◇ (y ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3:G), ((q0 ◇ (q1 ◇ q2)) ◇ (((q1 ◇ q0) ◇ q0) ◇ q3)) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ (((q1 ◇ q0) ◇ q0) ◇ q3)) (congrArg (fun t => t ◇ (q1 ◇ q2)) ((h q0 q1 q2).symm))).symm).trans ((h (q1 ◇ q2) ((q1 ◇ q0) ◇ q0) q3).symm)
  have apc1 : forall (q4 q5 q6:G), ((q4 ◇ (q5 ◇ q6)) ◇ q4) = (q5 ◇ q6):=by
    intro q4 q5 q6
    exact ((congrArg (fun t => (q4 ◇ (q5 ◇ q6)) ◇ t) ((h q4 q5 q4).symm)).symm).trans (apc0 q4 q5 q6 (q5 ◇ q4))
  have apc2 : forall (q7 q8 q9:G), ((q7 ◇ q8) ◇ ((q7 ◇ q8) ◇ q9)) = (q7 ◇ q8):=by
    intro q7 q8 q9
    exact ((congrArg (fun t => t ◇ ((q7 ◇ q8) ◇ q9)) (apc1 (q7 ◇ q8) q7 q8)).symm).trans ((h (q7 ◇ q8) (q7 ◇ q8) q9).symm)
  have apc4 : forall (x y z:G), (((y ◇ x) ◇ x) ◇ (y ◇ z)) = (((x ◇ x) ◇ x) ◇ (x ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc5 : forall (q10:G), (((q10 ◇ q10) ◇ q10) ◇ (q10 ◇ q10)) = q10:=by
    intro q10
    exact ((apc4 q10 q10 q10).symm).trans ((h q10 q10 q10).symm)
  have apc6 : forall (q11 q12:G), (q11 ◇ (q11 ◇ q12)) = q11:=by
    intro q11 q12
    exact ((congrArg (fun t => q11 ◇ t) (congrArg (fun t => t ◇ q12) (apc5 q11))).symm).trans ((((congrArg (fun t => t ◇ ((((q11 ◇ q11) ◇ q11) ◇ (q11 ◇ q11)) ◇ q12)) (apc5 q11)).symm).trans (apc2 ((q11 ◇ q11) ◇ q11) (q11 ◇ q11) q12)).trans (apc5 q11))
  have apc7 : forall (q13 q14:G), ((q14 ◇ q13) ◇ q14) = q13:=by
    intro q13 q14
    exact (((congrArg (fun t => t ◇ q14) (congrArg (fun t => q14 ◇ t) (apc5 q13))).symm).trans (apc1 q14 ((q13 ◇ q13) ◇ q13) (q13 ◇ q13))).trans (apc5 q13)
  have apc9 : forall (q1 q2 q3:G), ((q1 ◇ q2) ◇ (q1 ◇ q3)) = (q1 ◇ q2):=by
    intro q1 q2 q3
    exact ((congrArg (fun t => (q1 ◇ q2) ◇ t) (congrArg (fun t => t ◇ q3) (apc6 q1 q2))).symm).trans (((congrArg (fun t => t ◇ ((q1 ◇ (q1 ◇ q2)) ◇ q3)) ((h (q1 ◇ q2) q1 q2).symm)).symm).trans ((h (q1 ◇ q2) (q1 ◇ (q1 ◇ q2)) q3).symm))
  have apc11 : forall (q15 q16 q17:G), ((q15 ◇ q16) ◇ q17) = q17:=by
    intro q15 q16 q17
    exact (((apc7 q17 (q15 ◇ q16)).symm).trans (((congrArg (fun t => ((q15 ◇ q16) ◇ q17) ◇ t) (apc9 q15 q16 q15)).symm).trans (apc9 (q15 ◇ q16) q17 (q15 ◇ q15)))).symm
  have apc12 : forall (q18 q19 q20:G), q19 = q18:=by
    intro q18 q19 q20
    exact (((congrArg (fun t => (q20 ◇ q18) ◇ t) (apc11 q18 q20 q19)).trans (apc11 q20 q18 q19)).symm).trans (((congrArg (fun t => t ◇ ((q18 ◇ q20) ◇ q19)) (congrArg (fun t => t ◇ q18) (apc7 q20 q18))).symm).trans ((h q18 (q18 ◇ q20) q19).symm))
  exact (apc12 x x x).trans ((apc12 x ((y ◇ (z ◇ (w ◇ u))) ◇ (y ◇ y)) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_2092_to_25713 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_2092_to_25713
