-- Equation47164 → Equation47482
-- Recorded verdict: true
-- Premise: x * y = (y * x) * ((y * z) * w)
-- Conclusion: x * y = (z * z) * ((y * w) * w)
-- Original submission SHA-256: d7474350f19c681d5be0814d2c14e5db8bf8fc0b27e5edba47948703a4f8812e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ x) ◇ ((y ◇ z) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ z) ◇ ((y ◇ w) ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ (q2 ◇ q1)) = (q0 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q1 ◇ q0) ◇ t) ((h q2 q1 q0 q0).symm)).symm).trans ((h q0 q1 q2 ((q1 ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5 q0:G), (((q4 ◇ q3) ◇ q0) ◇ ((q3 ◇ q4) ◇ q5)) = (q0 ◇ (q4 ◇ q3)):=by
    intro q3 q4 q5 q0
    exact ((congrArg (fun t => ((q4 ◇ q3) ◇ q0) ◇ t) (congrArg (fun t => t ◇ q5) ((h q3 q4 q3 q3).symm))).symm).trans ((h q0 (q4 ◇ q3) ((q4 ◇ q3) ◇ q3) q5).symm)
  have apc2 : forall (q6 q7 q8 q9:G), ((q7 ◇ q8) ◇ ((q7 ◇ q8) ◇ q9)) = ((q6 ◇ q8) ◇ (q8 ◇ q7)):=by
    intro q6 q7 q8 q9
    exact ((congrArg (fun t => t ◇ ((q7 ◇ q8) ◇ q9)) (apc0 q7 q8 q6)).symm).trans (apc1 q7 q8 q9 (q6 ◇ q8))
  have apc4 : forall (q10 q11 q12:G), ((q10 ◇ q12) ◇ (q12 ◇ q11)) = (q12 ◇ q11):=by
    intro q10 q11 q12
    exact ((apc2 q10 q11 q12 q10).symm).trans ((h q12 q11 q12 q10).symm)
  have apc5 : forall (q13 q14 q15 q16:G), ((q15 ◇ q14) ◇ (q16 ◇ q13)) = (q14 ◇ q15):=by
    intro q13 q14 q15 q16
    exact ((congrArg (fun t => (q15 ◇ q14) ◇ t) (apc4 q15 q13 q16)).symm).trans ((h q14 q15 q16 (q16 ◇ q13)).symm)
  have apc6 : forall (q17 q18 q19:G), ((q18 ◇ q17) ◇ q19) = (q17 ◇ q18):=by
    intro q17 q18 q19
    exact (((apc5 q19 q17 q18 (q18 ◇ q17)).symm).trans (((congrArg (fun t => t ◇ ((q18 ◇ q17) ◇ q19)) (apc4 q17 q17 q18)).symm).trans (apc4 (q17 ◇ q18) q19 (q18 ◇ q17)))).symm
  have apc9 : forall (q20 q21 q22 q23 q24 q25:G), (q22 ◇ q21) = (q20 ◇ q23):=by
    intro q20 q21 q22 q23 q24 q25
    exact ((((congrArg (fun t => (q21 ◇ q22) ◇ t) (congrArg (fun t => t ◇ q24) (apc6 q21 q22 q25))).trans (congrArg (fun t => (q21 ◇ q22) ◇ t) (apc6 q22 q21 q24))).trans (apc6 q22 q21 (q22 ◇ q21))).symm).trans ((((congrArg (fun t => t ◇ (((q22 ◇ q21) ◇ q25) ◇ q24)) (apc5 q20 q21 q22 q23)).symm).trans ((h (q23 ◇ q20) (q22 ◇ q21) q25 q24).symm)).trans (apc6 q20 q23 (q22 ◇ q21)))
  exact (apc9 (x ◇ y) y x ((z ◇ z) ◇ ((y ◇ w) ◇ w)) (x ◇ y) (x ◇ y)).trans ((apc9 (x ◇ y) ((y ◇ w) ◇ w) (z ◇ z) ((z ◇ z) ◇ ((y ◇ w) ◇ w)) (x ◇ y) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47164_to_47482 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47164_to_47482
