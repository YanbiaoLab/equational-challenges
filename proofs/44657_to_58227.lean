-- Equation44657 → Equation58227
-- Recorded verdict: true
-- Premise: x * y = y * ((z * (w * w)) * w)
-- Conclusion: (x * x) * x = y * (z * (x * x))
-- Original submission SHA-256: 610178119cb6f8473242d0e957ce319a301f1f268ac0ba88a83506fb0cb9c716
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ ((z ◇ (w ◇ w)) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ x = y ◇ (z ◇ (x ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ q0)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) ((apc0 (q0 ◇ (q0 ◇ q0)) q0 q0 q0).symm)).symm).trans ((h q1 q2 q0 q0).symm)
  have apc2 : forall (q3 q4 q5 q6:G), (q6 ◇ (q4 ◇ (q3 ◇ q3))) = (q5 ◇ q6):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => q6 ◇ t) (apc1 q3 q4 (q3 ◇ q3))).symm).trans (apc1 (q3 ◇ q3) q5 q6)
  have apc3 : forall (q7 q8 q9:G), (q9 ◇ (q8 ◇ (q7 ◇ q7))) = (q9 ◇ q9):=by
    intro q7 q8 q9
    exact (apc2 q7 q8 q7 q9).trans ((apc0 q7 q9 q7 q7).symm)
  have apc8 : forall (q10 q11 q12:G), (q12 ◇ (q10 ◇ q11)) = (q12 ◇ q12):=by
    intro q10 q11 q12
    exact ((congrArg (fun t => q12 ◇ t) (apc1 q10 q10 q11)).symm).trans (apc3 q10 q11 q12)
  have apc9 : forall (q13 q14 q15:G), (q14 ◇ q15) = (q13 ◇ q15):=by
    intro q13 q14 q15
    exact ((h q13 q15 q13 q13).trans ((h q14 q15 q13 q13).symm)).symm
  have apc10 : forall (q16 q17 q18 q19 q20:G), (q17 ◇ q18) = (q16 ◇ q16):=by
    intro q16 q17 q18 q19 q20
    exact ((((congrArg (fun t => q16 ◇ t) (congrArg (fun t => t ◇ q19) (apc8 q19 q19 q20))).trans (apc8 (q20 ◇ q20) q19 q16)).symm).trans (((apc9 q16 q18 ((q20 ◇ (q19 ◇ q19)) ◇ q19)).symm).trans ((h q17 q18 q20 q19).symm))).symm
  exact (apc10 ((x ◇ x) ◇ x) (x ◇ x) x ((x ◇ x) ◇ x) ((x ◇ x) ◇ x)).trans ((apc10 ((x ◇ x) ◇ x) y (z ◇ (x ◇ x)) ((x ◇ x) ◇ x) ((x ◇ x) ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_44657_to_58227 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_44657_to_58227
