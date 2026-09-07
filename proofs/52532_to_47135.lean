-- Equation52532 → Equation47135
-- Recorded verdict: true
-- Premise: x * y = ((y * (z * w)) * x) * x
-- Conclusion: x * y = (x * z) * ((w * w) * y)
-- Original submission SHA-256: b6c61fa9e758488a7ba6a936dda640367f539368b60f852c1957bab4278060d2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((y ◇ (z ◇ w)) ◇ x) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (x ◇ z) ◇ ((w ◇ w) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc4 : forall (q0 q1 q2 q3 q4 q5:G), (q4 ◇ ((q1 ◇ (q2 ◇ q0)) ◇ (q5 ◇ q3))) = ((((q5 ◇ q3) ◇ q1) ◇ q4) ◇ q4):=by
    intro q0 q1 q2 q3 q4 q5
    exact (((congrArg (fun t => t ◇ q4) (congrArg (fun t => t ◇ q4) ((h (q5 ◇ q3) q1 q2 q0).symm))).symm).trans ((h q4 ((q1 ◇ (q2 ◇ q0)) ◇ (q5 ◇ q3)) q5 q3).symm)).symm
  have apc6 : forall (q6 q7 q8 q9 q10:G), ((((((q8 ◇ q7) ◇ q6) ◇ q10) ◇ q10) ◇ q9) ◇ q9) = (q9 ◇ q10):=by
    intro q6 q7 q8 q9 q10
    exact ((congrArg (fun t => t ◇ q9) (congrArg (fun t => t ◇ q9) (apc4 q6 q6 q6 q7 q10 q8))).symm).trans ((h q9 q10 (q6 ◇ (q6 ◇ q6)) (q8 ◇ q7)).symm)
  have apc7 : forall (q11:G), ((q11 ◇ q11) ◇ q11) = (q11 ◇ q11):=by
    intro q11
    exact ((congrArg (fun t => t ◇ q11) (apc6 q11 q11 q11 q11 q11)).symm).trans (apc6 q11 q11 (q11 ◇ q11) q11 q11)
  have apc8 : forall (q12 q11 q13:G), (((q13 ◇ q12) ◇ q11) ◇ q11) = (q11 ◇ q13):=by
    intro q12 q11 q13
    exact ((congrArg (fun t => t ◇ q11) (congrArg (fun t => t ◇ q11) (apc6 q12 q12 q12 q13 q12))).symm).trans (apc6 q12 q12 ((q12 ◇ q12) ◇ q12) q11 q13)
  have apc9 : forall (q14 q15 q16 q17:G), (q17 ◇ ((q15 ◇ q14) ◇ q16)) = (q17 ◇ q16):=by
    intro q14 q15 q16 q17
    exact (((apc8 q15 q17 q16).symm).trans (((congrArg (fun t => t ◇ q17) (congrArg (fun t => t ◇ q17) (apc8 q14 q16 q15))).symm).trans (apc8 q16 q17 ((q15 ◇ q14) ◇ q16)))).symm
  have apc11 : forall (q18 q19 q20:G), ((q19 ◇ q18) ◇ q19) = (q19 ◇ q18):=by
    intro q18 q19 q20
    exact (((congrArg (fun t => t ◇ q19) (apc9 q20 q18 q19 ((q18 ◇ q20) ◇ q19))).trans (congrArg (fun t => t ◇ q19) (apc8 q20 q19 q18))).symm).trans ((((apc9 q20 q18 q19 (((q18 ◇ q20) ◇ q19) ◇ ((q18 ◇ q20) ◇ q19))).symm).trans (apc7 ((q18 ◇ q20) ◇ q19))).trans ((apc9 q20 q18 q19 ((q18 ◇ q20) ◇ q19)).trans (apc8 q20 q19 q18)))
  have apc12 : forall (q21 q22:G), ((q22 ◇ q21) ◇ (q22 ◇ q21)) = (q22 ◇ q21):=by
    intro q21 q22
    exact (((congrArg (fun t => t ◇ (q22 ◇ q21)) (apc11 q21 q22 q21)).symm).trans (apc11 q22 (q22 ◇ q21) q21)).trans (apc11 q21 q22 ((q22 ◇ q21) ◇ q22))
  have apc13 : forall (q23 q24 q25:G), ((q24 ◇ q23) ◇ q25) = (q25 ◇ q24):=by
    intro q23 q24 q25
    exact (((apc12 q25 (q24 ◇ q23)).symm).trans (apc9 q23 q24 q25 ((q24 ◇ q23) ◇ q25))).trans (apc8 q23 q25 q24)
  exact (calc
    (x ◇ y) = (x ◇ y):=rfl
    _ = ((x ◇ z) ◇ ((w ◇ w) ◇ y)):=(((congrArg (fun t => (x ◇ z) ◇ t) (apc13 w w y)).trans (apc13 z x (y ◇ w))).trans (apc13 w y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52532_to_47135 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52532_to_47135
