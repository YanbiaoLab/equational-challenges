-- Equation5891 → Equation6071
-- Recorded verdict: true
-- Premise: x = y * (x * (z * ((z * z) * x)))
-- Conclusion: x = y * (y * (z * ((w * u) * x)))
-- Original submission SHA-256: bcfa8f7a0a1351548b21677d0c7912a1fd6ac4210340eda59fb79080f46e5472
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (z ◇ ((z ◇ z) ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ (y ◇ (z ◇ ((w ◇ u) ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1:G), (((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1
    exact (((congrArg (fun t => q0 ◇ t) ((h q1 (((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ q1) (q1 ◇ q1)).symm)).symm).trans ((h (((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ q1) q0 q1).symm)).symm
  have apc1 : forall (q0 q1:G), (q1 ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1
    exact (((apc0 q0 q1).symm).trans (apc0 q1 q1)).symm
  have apc2 : forall (q2 q3 q4:G), (q3 ◇ q4) = (q2 ◇ q4):=by
    intro q2 q3 q4
    exact (((apc0 q2 q4).symm).trans (apc0 q3 q4)).symm
  have apc7 : forall (q5 q6 q7:G), (q6 ◇ (q5 ◇ (q7 ◇ (q5 ◇ q5)))) = q5:=by
    intro q5 q6 q7
    exact ((congrArg (fun t => q6 ◇ t) (congrArg (fun t => q5 ◇ t) (congrArg (fun t => q7 ◇ t) ((apc1 (q7 ◇ q7) q5).symm)))).symm).trans ((h q5 q6 q7).symm)
  have apc8 : forall (q8 q9 q10 q11:G), (q10 ◇ (q9 ◇ (q11 ◇ (q8 ◇ q9)))) = q9:=by
    intro q8 q9 q10 q11
    exact ((congrArg (fun t => q10 ◇ t) (congrArg (fun t => q9 ◇ t) (congrArg (fun t => q11 ◇ t) (apc2 q8 (q11 ◇ q11) q9)))).symm).trans ((h q9 q10 q11).symm)
  have apc9 : forall (q12 q13 q14:G), ((q12 ◇ q12) ◇ q14) = (q13 ◇ q14):=by
    intro q12 q13 q14
    exact (((congrArg (fun t => q13 ◇ t) ((h q14 ((q12 ◇ q12) ◇ q14) q12).symm)).symm).trans (apc8 q12 ((q12 ◇ q12) ◇ q14) q13 q14)).symm
  have apc11 : forall (q15 q16:G), ((q15 ◇ q15) ◇ q16) = (q16 ◇ q16):=by
    intro q15 q16
    exact (apc9 q15 q15 q16).trans ((apc1 q15 q16).symm)
  have apc12 : forall (q17 q18 q19 q20:G), ((q17 ◇ q18) ◇ q20) = (q19 ◇ q20):=by
    intro q17 q18 q19 q20
    exact ((congrArg (fun t => t ◇ q20) (apc1 q17 q18)).symm).trans (apc9 q18 q19 q20)
  have apc16 : forall (q21 q22 q23:G), ((q21 ◇ q22) ◇ q23) = (q23 ◇ q23):=by
    intro q21 q22 q23
    exact ((congrArg (fun t => t ◇ q23) (apc1 q21 q22)).symm).trans (apc11 q22 q23)
  have apc17 : forall (q24 q25 q26 q27:G), (q27 ◇ (q24 ◇ q25)) = (q26 ◇ (q24 ◇ q25)):=by
    intro q24 q25 q26 q27
    exact (((apc12 q24 q25 q26 (q24 ◇ q25)).symm).trans (apc1 q27 (q24 ◇ q25))).symm
  have apc21 : forall (q24 q25 q26 q27:G), (q26 ◇ (q24 ◇ q25)) = (q24 ◇ (q24 ◇ q25)):=by
    intro q24 q25 q26 q27
    exact ((apc17 q24 q25 q26 q24).symm).trans (apc17 q24 q25 q24 q24)
  have apc25 : forall (q28 q29:G), (q28 ◇ (q28 ◇ (q29 ◇ (q29 ◇ q29)))) = q29:=by
    intro q28 q29
    exact (((congrArg (fun t => q28 ◇ t) (congrArg (fun t => q28 ◇ t) (apc21 q29 q29 q28 (q28 ◇ (q29 ◇ q29))))).trans (apc21 q28 (q29 ◇ (q29 ◇ q29)) q28 (q28 ◇ (q28 ◇ (q29 ◇ (q29 ◇ q29)))))).symm).trans (((congrArg (fun t => q28 ◇ t) (apc2 q28 q29 (q28 ◇ (q29 ◇ q29)))).symm).trans (apc7 q29 q28 q28))
  exact (calc
    x = x:=rfl
    _ = (y ◇ (y ◇ (z ◇ ((w ◇ u) ◇ x)))):=(((((congrArg (fun t => y ◇ t) (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (apc16 w u x)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => y ◇ t) (apc21 x x z (z ◇ (x ◇ x)))))).trans (congrArg (fun t => y ◇ t) (apc21 x (x ◇ x) y (y ◇ (x ◇ (x ◇ x)))))).trans (apc21 x (x ◇ (x ◇ x)) y (y ◇ (x ◇ (x ◇ (x ◇ x)))))).trans (apc25 x x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5891_to_6071 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5891_to_6071
