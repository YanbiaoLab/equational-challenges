-- Equation5710 → Equation5577
-- Recorded verdict: true
-- Premise: x = x ◇ (y ◇ (z ◇ ((x ◇ w) ◇ x)))
-- Conclusion: x = x ◇ (x ◇ (x ◇ ((y ◇ x) ◇ x)))
-- Original submission SHA-256: 0d39073514638755944cf51b632b286f7bce597339ecb421a3d778d49e599abb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (y ◇ (z ◇ ((x ◇ w) ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = x ◇ (x ◇ (x ◇ ((y ◇ x) ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc1 : forall (q0 q1 q2:G), (q0 ◇ (q1 ◇ (q2 ◇ (q0 ◇ q0)))) = q0:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q0 ◇ t) (congrArg (fun t => q1 ◇ t) (congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ q0) ((h q0 q0 q0 q0).symm))))).symm).trans ((h q0 q1 q2 (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0)))).symm)
  have apc3 : forall (q3 q4 q5:G), ((q3 ◇ (q5 ◇ q5)) ◇ (q4 ◇ q5)) = (q3 ◇ (q5 ◇ q5)):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => (q3 ◇ (q5 ◇ q5)) ◇ t) (congrArg (fun t => q4 ◇ t) (apc1 q5 (q3 ◇ (q5 ◇ q5)) q3))).symm).trans (apc1 (q3 ◇ (q5 ◇ q5)) q4 q5)
  have apc7 : forall (q6 q7 q8 q9:G), ((q6 ◇ q7) ◇ (q8 ◇ (q9 ◇ ((q6 ◇ q7) ◇ (q7 ◇ q7))))) = (q6 ◇ q7):=by
    intro q6 q7 q8 q9
    exact ((congrArg (fun t => (q6 ◇ q7) ◇ t) (congrArg (fun t => q8 ◇ t) (congrArg (fun t => q9 ◇ t) (apc3 (q6 ◇ q7) q6 q7)))).symm).trans ((h (q6 ◇ q7) q8 q9 (q7 ◇ q7)).symm)
  have apc15 : forall (q10 q11 q12 q13:G), ((q13 ◇ ((q11 ◇ q12) ◇ (q11 ◇ q12))) ◇ (q10 ◇ (q12 ◇ q12))) = (q13 ◇ ((q11 ◇ q12) ◇ (q11 ◇ q12))):=by
    intro q10 q11 q12 q13
    exact ((congrArg (fun t => (q13 ◇ ((q11 ◇ q12) ◇ (q11 ◇ q12))) ◇ t) (apc3 q10 q11 q12)).symm).trans (apc3 q13 (q10 ◇ (q12 ◇ q12)) (q11 ◇ q12))
  have apc16 : forall (q14 q15 q16:G), (q16 ◇ (q15 ◇ ((q14 ◇ q16) ◇ (q14 ◇ q16)))) = q16:=by
    intro q14 q15 q16
    exact ((congrArg (fun t => q16 ◇ t) (apc15 q14 q14 q16 q15)).symm).trans (apc1 q16 (q15 ◇ ((q14 ◇ q16) ◇ (q14 ◇ q16))) q14)
  have apc17 : forall (q17 q18 q19 q20:G), ((q18 ◇ (q17 ◇ q20)) ◇ (q19 ◇ q20)) = (q18 ◇ (q17 ◇ q20)):=by
    intro q17 q18 q19 q20
    exact ((congrArg (fun t => (q18 ◇ (q17 ◇ q20)) ◇ t) (congrArg (fun t => q19 ◇ t) (apc16 q17 (q18 ◇ (q17 ◇ q20)) q20))).symm).trans (apc7 q18 (q17 ◇ q20) q19 q20)
  have apc18 : forall (q21 q22 q23 q24:G), (q23 ◇ (q24 ◇ (q22 ◇ (q21 ◇ q23)))) = q23:=by
    intro q21 q22 q23 q24
    exact ((congrArg (fun t => q23 ◇ t) (congrArg (fun t => q24 ◇ t) (apc17 q21 q22 q23 q23))).symm).trans (apc1 q23 q24 (q22 ◇ (q21 ◇ q23)))
  exact (apc18 (y ◇ x) x x x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5710_to_5577 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5710_to_5577
