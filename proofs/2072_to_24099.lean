-- Equation2072 → Equation24099
-- Recorded verdict: true
-- Premise: x = ((x * y) * z) * (x * z)
-- Conclusion: x = ((x * y) * y) * ((z * x) * y)
-- Original submission SHA-256: 1a265de9eecc92f3608feace6d481a573907255153903720e4976504c1e28e9b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ y) ◇ z) ◇ (x ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ y) ◇ y) ◇ ((z ◇ x) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q0 ◇ ((q0 ◇ q1) ◇ (q0 ◇ q2))) = (q0 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ ((q0 ◇ q1) ◇ (q0 ◇ q2))) ((h q0 q1 q2).symm)).symm).trans ((h (q0 ◇ q1) q2 (q0 ◇ q2)).symm)
  have apc1 : forall (x y z:G), (((x ◇ y) ◇ z) ◇ (x ◇ z)) = (((x ◇ x) ◇ x) ◇ (x ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc2 : forall (q3:G), (((q3 ◇ q3) ◇ q3) ◇ (q3 ◇ q3)) = q3:=by
    intro q3
    exact ((apc1 q3 q3 q3).symm).trans ((h q3 q3 q3).symm)
  have apc3 : forall (q0 q1 q4 q5:G), ((q0 ◇ q5) ◇ (((q0 ◇ q1) ◇ q4) ◇ q5)) = ((q0 ◇ q1) ◇ q4):=by
    intro q0 q1 q4 q5
    exact ((congrArg (fun t => t ◇ (((q0 ◇ q1) ◇ q4) ◇ q5)) (congrArg (fun t => t ◇ q5) ((h q0 q1 q4).symm))).symm).trans ((h ((q0 ◇ q1) ◇ q4) (q0 ◇ q4) q5).symm)
  have apc4 : forall (q6 q7 q8:G), ((q6 ◇ (q6 ◇ q8)) ◇ q6) = ((q6 ◇ q7) ◇ q8):=by
    intro q6 q7 q8
    exact ((congrArg (fun t => (q6 ◇ (q6 ◇ q8)) ◇ t) ((h q6 q7 q8).symm)).symm).trans (apc3 q6 q7 q8 (q6 ◇ q8))
  have apc5 : forall (q9 q10 q11 q12:G), ((q10 ◇ q11) ◇ q12) = ((q10 ◇ q9) ◇ q12):=by
    intro q9 q10 q11 q12
    exact (((apc4 q10 q9 q12).symm).trans (apc4 q10 q11 q12)).symm
  have apc6 : forall (q13 q14 q15 q16:G), (q14 ◇ q15) = (q14 ◇ q13):=by
    intro q13 q14 q15 q16
    exact (((apc0 q14 q13 q16).symm).trans (((congrArg (fun t => q14 ◇ t) (apc5 q13 q14 q15 (q14 ◇ q16))).symm).trans (apc0 q14 q15 q16))).symm
  have apc8 : forall (q6 q7 q8:G), ((q6 ◇ q7) ◇ q8) = ((q6 ◇ q6) ◇ q8):=by
    intro q6 q7 q8
    exact ((apc4 q6 q7 q8).symm).trans (apc4 q6 q6 q8)
  have apc16 : forall (q6 q8 q7:G), ((q6 ◇ q6) ◇ q8) = ((q6 ◇ q6) ◇ q6):=by
    intro q6 q8 q7
    exact (((apc8 q6 (q6 ◇ q8) q6).symm).trans ((apc4 q6 q7 q8).trans (apc8 q6 q7 q8))).symm
  have apc18 : forall (q17 q18 q19 q20:G), ((q17 ◇ q18) ◇ q19) = ((q17 ◇ q17) ◇ q17):=by
    intro q17 q18 q19 q20
    exact (((apc16 q17 q20 ((q17 ◇ q17) ◇ q20)).symm).trans (((apc8 q17 q18 q20).symm).trans (apc6 q19 (q17 ◇ q18) q20 q17))).symm
  exact (calc
    x = x:=rfl
    _ = (((x ◇ y) ◇ y) ◇ ((z ◇ x) ◇ y)):=((((congrArg (fun t => t ◇ ((z ◇ x) ◇ y)) (apc18 x y y ((x ◇ y) ◇ y))).trans (apc18 (x ◇ x) x ((z ◇ x) ◇ y) (((x ◇ x) ◇ x) ◇ ((z ◇ x) ◇ y)))).trans (congrArg (fun t => t ◇ (x ◇ x)) (apc18 x x (x ◇ x) ((x ◇ x) ◇ (x ◇ x))))).trans (apc2 x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_2072_to_24099 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_2072_to_24099
