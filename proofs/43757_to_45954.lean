-- Equation43757 → Equation45954
-- Recorded verdict: true
-- Premise: x * y = y * ((z * z) * (w * x))
-- Conclusion: x * x = (x * y) * (z * (y * y))
-- Original submission SHA-256: d48bd406df18a4e5cdaeaad0543c023ca9fe612ad7d4b44c62b2c6596f49f6ef
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ ((z ◇ z) ◇ (w ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (x ◇ y) ◇ (z ◇ (y ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ (q1 ◇ (q3 ◇ q3))) = ((q0 ◇ q1) ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) ((h q1 (q3 ◇ q3) q0 q0).symm)).symm).trans ((h (q0 ◇ q1) q2 q3 (q0 ◇ q0)).symm)
  have apc1 : forall (q4 q5 q6 q7:G), (q7 ◇ (q4 ◇ q6)) = ((q5 ◇ q6) ◇ q7):=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => q7 ◇ t) ((h q4 q6 q4 q4).symm)).symm).trans (apc0 q5 q6 q7 (q4 ◇ q4))
  have apc2 : forall (q8 q9 q10 q11:G), (q10 ◇ ((q8 ◇ q9) ◇ (q11 ◇ q11))) = (q9 ◇ q10):=by
    intro q8 q9 q10 q11
    exact ((congrArg (fun t => q10 ◇ t) (apc1 q8 q8 q9 (q11 ◇ q11))).symm).trans ((h q9 q10 q11 q8).symm)
  have apc3 : forall (q12 q13 q14 q15:G), (q15 ◇ (q12 ◇ (q13 ◇ q14))) = (q14 ◇ q15):=by
    intro q12 q13 q14 q15
    exact ((congrArg (fun t => q15 ◇ t) ((h q12 (q13 ◇ q14) q12 q12).symm)).symm).trans (apc2 q13 q14 q15 (q12 ◇ q12))
  have apc5 : forall (q16 q17 q18 q19 q20:G), (q19 ◇ (q16 ◇ q17)) = (q18 ◇ q19):=by
    intro q16 q17 q18 q19 q20
    exact ((congrArg (fun t => q19 ◇ t) (apc3 q18 q20 q16 q17)).symm).trans (((congrArg (fun t => q19 ◇ t) (congrArg (fun t => q17 ◇ t) ((apc1 q20 q20 q16 q18).symm))).symm).trans (apc3 q17 (q20 ◇ q16) q18 q19))
  exact ((apc5 x y x x (x ◇ x)).symm).trans ((apc5 z (y ◇ y) x (x ◇ y) (x ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43757_to_45954 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43757_to_45954
