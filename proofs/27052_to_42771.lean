-- Equation27052 → Equation42771
-- Recorded verdict: true
-- Premise: x = ((y * y) * (z * x)) * (y * x)
-- Conclusion: x * y = y * (x * ((y * x) * y))
-- Original submission SHA-256: 8a23b23de8255fed7d10cc8a4a8b00112099917ba35e57de13ea5d9f1b823002
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ (z ◇ x)) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = y ◇ (x ◇ ((y ◇ x) ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0:G), (q0 ◇ ((q0 ◇ q0) ◇ q0)) = q0:=by
    intro q0
    exact ((congrArg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) ((h q0 q0 q0).symm)).symm).trans ((h q0 (q0 ◇ q0) q0).symm)
  have apc1 : forall (q1:G), ((q1 ◇ q1) ◇ q1) = (q1 ◇ q1):=by
    intro q1
    exact ((congrArg (fun t => (q1 ◇ q1) ◇ t) ((h q1 q1 q1).symm)).symm).trans (apc0 (q1 ◇ q1))
  have apc5 : forall (q2 q3 q4:G), (((q4 ◇ q4) ◇ q2) ◇ (q4 ◇ (q3 ◇ q2))) = (q3 ◇ q2):=by
    intro q2 q3 q4
    exact ((congrArg (fun t => t ◇ (q4 ◇ (q3 ◇ q2))) (congrArg (fun t => (q4 ◇ q4) ◇ t) ((h q2 q3 q2).symm))).symm).trans ((h (q3 ◇ q2) q4 ((q3 ◇ q3) ◇ (q2 ◇ q2))).symm)
  have apc6 : forall (q5 q6:G), ((q5 ◇ q5) ◇ (q5 ◇ (q6 ◇ q5))) = (q6 ◇ q5):=by
    intro q5 q6
    exact ((congrArg (fun t => t ◇ (q5 ◇ (q6 ◇ q5))) (apc1 q5)).symm).trans (apc5 q5 q6 q5)
  have apc7 : forall (q7 q8:G), ((q7 ◇ q8) ◇ (q8 ◇ (q7 ◇ q8))) = (q7 ◇ q8):=by
    intro q7 q8
    exact ((congrArg (fun t => t ◇ (q8 ◇ (q7 ◇ q8))) (apc6 q8 q7)).symm).trans ((h (q7 ◇ q8) q8 q8).symm)
  have apc8 : forall (q9 q10:G), ((q9 ◇ q10) ◇ (q9 ◇ q10)) = (q10 ◇ (q9 ◇ q10)):=by
    intro q9 q10
    exact ((apc1 (q9 ◇ q10)).symm).trans (((congrArg (fun t => ((q9 ◇ q10) ◇ (q9 ◇ q10)) ◇ t) (apc7 q9 q10)).symm).trans (apc6 (q9 ◇ q10) q10))
  have apc11 : forall (q11 q12:G), (((q12 ◇ q12) ◇ (q11 ◇ q11)) ◇ (q12 ◇ q11)) = q11:=by
    intro q11 q12
    exact ((congrArg (fun t => t ◇ (q12 ◇ q11)) (congrArg (fun t => (q12 ◇ q12) ◇ t) (apc1 q11))).symm).trans ((h q11 q12 (q11 ◇ q11)).symm)
  have apc12 : forall (q13 q14:G), ((q14 ◇ q13) ◇ q13) = (q13 ◇ q13):=by
    intro q13 q14
    exact (((congrArg (fun t => q13 ◇ t) (apc11 q13 q14)).symm).trans ((((congrArg (fun t => t ◇ (((q14 ◇ q14) ◇ (q13 ◇ q13)) ◇ (q14 ◇ q13))) (apc11 q13 q14)).symm).trans (apc8 ((q14 ◇ q14) ◇ (q13 ◇ q13)) (q14 ◇ q13))).trans (congrArg (fun t => (q14 ◇ q13) ◇ t) (apc11 q13 q14)))).symm
  have apc13 : forall (q15 q16:G), (q15 ◇ (q16 ◇ q15)) = q15:=by
    intro q15 q16
    exact ((apc8 q16 q15).symm).trans (((apc12 (q16 ◇ q15) (q16 ◇ q16)).symm).trans ((h q15 q16 q16).symm))
  have apc14 : forall (q17 q18:G), (q18 ◇ q18) = (q17 ◇ q18):=by
    intro q17 q18
    exact ((apc12 q18 q17).symm).trans (((congrArg (fun t => (q17 ◇ q18) ◇ t) (apc13 q18 q17)).symm).trans (apc13 (q17 ◇ q18) q18))
  have apc15 : forall (q19 q20 q21:G), (q20 ◇ q21) = (q19 ◇ q21):=by
    intro q19 q20 q21
    exact (((apc14 q19 q21).symm).trans (apc14 q20 q21)).symm
  have apc16 : forall (q22 q23 q24:G), (q22 ◇ (q24 ◇ q23)) = q23:=by
    intro q22 q23 q24
    exact ((apc15 q22 q23 (q24 ◇ q23)).symm).trans (apc13 q23 q24)
  exact (calc
    (x ◇ y) = (y ◇ y):=(apc14 x y).symm
    _ = (y ◇ (x ◇ ((y ◇ x) ◇ y))):=(congrArg (fun t => y ◇ t) (apc16 x y (y ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_27052_to_42771 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_27052_to_42771
