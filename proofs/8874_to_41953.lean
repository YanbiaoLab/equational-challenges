-- Equation8874 → Equation41953
-- Recorded verdict: true
-- Premise: x = y * (z * (((z * x) * w) * x))
-- Conclusion: x * y = y * (y * (z * (w * y)))
-- Original submission SHA-256: aa56b26134edb12ec22793b55a56ee1e764f9a3f7e28c095ebb3265ffae3217a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (z ◇ (((z ◇ x) ◇ w) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (y ◇ (z ◇ (w ◇ y)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ (q3 ◇ (q0 ◇ q1))) = q1:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ q1) ((h q0 (q3 ◇ q1) q0 q0).symm)))).symm).trans ((h q1 q2 q3 (q0 ◇ (((q0 ◇ q0) ◇ q0) ◇ q0))).symm)
  have apc1 : forall (q4 q5 q6:G), (q6 ◇ q5) = (q4 ◇ q5):=by
    intro q4 q5 q6
    exact ((congrArg (fun t => q6 ◇ t) (apc0 q4 q5 q4 q4)).symm).trans (apc0 q4 (q4 ◇ q5) q6 q4)
  have apc3 : forall (q4 q5 q7 q6 q8:G), (q6 ◇ (q8 ◇ q5)) = (q7 ◇ (q4 ◇ q5)):=by
    intro q4 q5 q7 q6 q8
    exact ((congrArg (fun t => q6 ◇ t) (congrArg (fun t => q8 ◇ t) (apc0 q4 q5 q4 q7))).symm).trans (apc0 q4 (q7 ◇ (q4 ◇ q5)) q6 q8)
  have apc4 : forall (q4 q5 q7 q6 q8:G), (q7 ◇ (q4 ◇ q5)) = (q5 ◇ (q5 ◇ q5)):=by
    intro q4 q5 q7 q6 q8
    exact ((apc3 q4 q5 q7 q4 q4).symm).trans (apc3 q5 q5 q5 q4 q4)
  have apc5 : forall (q4 q5 q7 q6 q8:G), (q5 ◇ (q5 ◇ q5)) = (q4 ◇ (q4 ◇ q5)):=by
    intro q4 q5 q7 q6 q8
    exact ((apc4 q8 q5 q6 (q6 ◇ (q8 ◇ q5)) (q6 ◇ (q8 ◇ q5))).symm).trans ((apc3 q4 q5 q4 q6 q8).trans ((apc3 q4 q5 q4 q4 q4).symm))
  have apc6 : forall (q9 q10 q11:G), (q10 ◇ (q11 ◇ q11)) = (q9 ◇ (q9 ◇ q11)):=by
    intro q9 q10 q11
    exact (((apc5 q9 q11 q9 q9 q9).symm).trans (apc1 q10 (q11 ◇ q11) q11)).symm
  have apc17 : forall (q12 q13 q14 q15:G), (q14 ◇ (q15 ◇ q15)) = (q12 ◇ (q13 ◇ q15)):=by
    intro q12 q13 q14 q15
    exact (((apc1 q12 (q13 ◇ q15) q13).symm).trans ((apc6 q13 q14 q15).symm)).symm
  have apc29 : forall (q16 q17 q18 q19 q20:G), (q19 ◇ (q20 ◇ (q16 ◇ (q17 ◇ q18)))) = (q18 ◇ q18):=by
    intro q16 q17 q18 q19 q20
    exact ((congrArg (fun t => q19 ◇ t) (congrArg (fun t => q20 ◇ t) (apc17 q16 q17 ((q20 ◇ (q18 ◇ q18)) ◇ q16) q18))).symm).trans ((h (q18 ◇ q18) q19 q20 q16).symm)
  exact (calc
    (x ◇ y) = (y ◇ y):=apc1 y y x
    _ = (w ◇ ((z ◇ (w ◇ y)) ◇ (z ◇ (w ◇ y)))):=(apc29 z w y w (z ◇ (w ◇ y))).symm
    _ = (y ◇ (y ◇ (z ◇ (w ◇ y)))):=((apc6 y w (z ◇ (w ◇ y))).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_8874_to_41953 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_8874_to_41953
