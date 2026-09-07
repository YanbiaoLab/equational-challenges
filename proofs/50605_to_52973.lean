-- Equation50605 → Equation52973
-- Recorded verdict: true
-- Premise: x * y = (x * ((z * y) * w)) * x
-- Conclusion: x * x = (((x * y) * z) * z) * x
-- Original submission SHA-256: a9cb88e921ebea7c430af92ae2c76dc98847466a31bdf3d9c1a2f8f6196902d0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (x ◇ ((z ◇ y) ◇ w)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (((x ◇ y) ◇ z) ◇ z) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), ((q2 ◇ ((q3 ◇ q0) ◇ q1)) ◇ q2) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q2) (congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ q1) ((h q3 q0 q0 q0).symm)))).symm).trans ((h q2 q3 (q3 ◇ ((q0 ◇ q0) ◇ q0)) q1).symm)
  have apc1 : forall (q4 q5 q6:G), (q4 ◇ q6) = (q4 ◇ q5):=by
    intro q4 q5 q6
    exact ((apc0 q5 q4 q4 q6).symm).trans ((h q4 q5 q6 q4).symm)
  have apc2 : forall (q7 q8 q9:G), ((q8 ◇ q7) ◇ q8) = (q8 ◇ q9):=by
    intro q7 q8 q9
    exact ((congrArg (fun t => t ◇ q8) (apc1 q8 q7 ((q7 ◇ q9) ◇ q7))).symm).trans ((h q8 q9 q7 q7).symm)
  have apc3 : forall (q10 q11 q12:G), (((q11 ◇ q10) ◇ q11) ◇ q11) = (q11 ◇ q12):=by
    intro q10 q11 q12
    exact ((congrArg (fun t => t ◇ q11) ((apc2 q10 q11 q10).symm)).symm).trans (apc2 q10 q11 q12)
  have apc5 : forall (x y z w:G), (x ◇ z) = (x ◇ x):=by
    intro x y z w
    exact ((apc0 y w x z).symm).trans ((((h x y z w).symm).trans (h x y x x)).trans (apc0 y x x x))
  have apc10 : forall (q13 q14 q15 q16:G), (((q15 ◇ q14) ◇ q13) ◇ q15) = (q15 ◇ q15):=by
    intro q13 q14 q15 q16
    exact (((congrArg (fun t => t ◇ q15) (apc1 (q15 ◇ q14) q13 q15)).symm).trans (apc3 q14 q15 q16)).trans (apc5 q15 (q15 ◇ q16) q16 (q15 ◇ q16))
  have apc13 : forall (q17 q18 q19 q20:G), (((q20 ◇ q17) ◇ q20) ◇ q19) = (q20 ◇ q18):=by
    intro q17 q18 q19 q20
    exact (((apc3 q17 q20 q18).symm).trans (apc1 ((q20 ◇ q17) ◇ q20) q19 q20)).symm
  have apc18 : forall (x y z w q7 q8 q9:G), ((q8 ◇ q7) ◇ q8) = (q8 ◇ q8):=by
    intro x y z w q7 q8 q9
    exact (apc2 q7 q8 q9).trans (apc5 q8 (q8 ◇ q9) q9 (q8 ◇ q9))
  have apc20 : forall (q21 q22 q23 q24:G), ((((q23 ◇ q23) ◇ q21) ◇ q22) ◇ q23) = (q23 ◇ q23):=by
    intro q21 q22 q23 q24
    exact ((congrArg (fun t => t ◇ q23) (congrArg (fun t => t ◇ q22) (congrArg (fun t => t ◇ q21) (apc18 ((q23 ◇ q24) ◇ q23) ((q23 ◇ q24) ◇ q23) ((q23 ◇ q24) ◇ q23) ((q23 ◇ q24) ◇ q23) q24 q23 ((q23 ◇ q24) ◇ q23))))).symm).trans (((congrArg (fun t => t ◇ q23) (congrArg (fun t => t ◇ q22) ((apc13 q24 q24 q21 q23).symm))).symm).trans (apc10 q22 q24 q23 q24))
  exact (calc
    (x ◇ x) = (x ◇ x):=rfl
    _ = ((((x ◇ y) ◇ z) ◇ z) ◇ x):=((congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ z) (apc5 x (x ◇ y) y (x ◇ y))))).trans (apc20 z z x ((((x ◇ x) ◇ z) ◇ z) ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50605_to_52973 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_50605_to_52973
