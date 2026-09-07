-- Equation5693 → Equation5644
-- Recorded verdict: true
-- Premise: x = x ◇ (y ◇ (y ◇ ((z ◇ w) ◇ x)))
-- Conclusion: x = x ◇ (y ◇ (x ◇ ((z ◇ x) ◇ x)))
-- Original submission SHA-256: 6f004c452d35736f8833ed547cda46bb6ca1c0c91e4237e8a27a76bde67eb949
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (y ◇ (y ◇ ((z ◇ w) ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (x ◇ ((z ◇ x) ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q0 ◇ (q1 ◇ (q1 ◇ (q2 ◇ q0)))) = q0:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q0 ◇ t) (congrArg (fun t => q1 ◇ t) (congrArg (fun t => q1 ◇ t) (congrArg (fun t => t ◇ q0) ((h q2 q0 q0 q0).symm))))).symm).trans ((h q0 q1 q2 (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q2)))).symm)
  have apc6 : forall (q3 q4 q5 q6:G), ((q3 ◇ (q3 ◇ (q4 ◇ q6))) ◇ (q5 ◇ (q5 ◇ q6))) = (q3 ◇ (q3 ◇ (q4 ◇ q6))):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => (q3 ◇ (q3 ◇ (q4 ◇ q6))) ◇ t) (congrArg (fun t => q5 ◇ t) (congrArg (fun t => q5 ◇ t) (apc0 q6 q3 q4)))).symm).trans (apc0 (q3 ◇ (q3 ◇ (q4 ◇ q6))) q5 q6)
  have apc7 : forall (q7 q8 q9 q10 q11:G), ((q8 ◇ (q8 ◇ q9)) ◇ (q10 ◇ (q10 ◇ (q11 ◇ (q11 ◇ (q7 ◇ q9)))))) = (q8 ◇ (q8 ◇ q9)):=by
    intro q7 q8 q9 q10 q11
    exact ((congrArg (fun t => (q8 ◇ (q8 ◇ q9)) ◇ t) (congrArg (fun t => q10 ◇ t) (congrArg (fun t => q10 ◇ t) (apc6 q11 q7 q8 q9)))).symm).trans ((h (q8 ◇ (q8 ◇ q9)) q10 q11 (q11 ◇ (q7 ◇ q9))).symm)
  have apc8 : forall (q12 q13 q14 q15 q16:G), (q14 ◇ (q15 ◇ (q15 ◇ (q16 ◇ (q16 ◇ (q13 ◇ (q14 ◇ (q12 ◇ q14)))))))) = q14:=by
    intro q12 q13 q14 q15 q16
    exact (((congrArg (fun t => t ◇ (q15 ◇ (q15 ◇ (q16 ◇ (q16 ◇ (q13 ◇ (q14 ◇ (q12 ◇ q14)))))))) (apc0 q14 q14 q12)).symm).trans (apc7 q13 q14 (q14 ◇ (q12 ◇ q14)) q15 q16)).trans (apc0 q14 q14 q12)
  have apc9 : forall (q17 q18 q19:G), (q19 ◇ (q18 ◇ (q19 ◇ (q17 ◇ q19)))) = q19:=by
    intro q17 q18 q19
    exact ((congrArg (fun t => q19 ◇ t) ((h (q18 ◇ (q19 ◇ (q17 ◇ q19))) (q18 ◇ (q19 ◇ (q17 ◇ q19))) q18 (q19 ◇ (q17 ◇ q19))).symm)).symm).trans (apc8 q17 q18 q19 (q18 ◇ (q19 ◇ (q17 ◇ q19))) (q18 ◇ (q19 ◇ (q17 ◇ q19))))
  exact (apc9 (z ◇ x) y x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5693_to_5644 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5693_to_5644
