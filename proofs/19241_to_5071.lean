-- Equation19241 → Equation5071
-- Recorded verdict: true
-- Premise: x = (y ◇ z) ◇ ((x ◇ x) ◇ (z ◇ y))
-- Conclusion: x = y ◇ (y ◇ (x ◇ (z ◇ (x ◇ z))))
-- Original submission SHA-256: 8343892376d19886a6be4095a4489a32a933a330e5f09166bf84d478ef368f5c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ ((x ◇ x) ◇ (z ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ (x ◇ (z ◇ (x ◇ z))))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), (((q1 ◇ q1) ◇ (q0 ◇ q0)) ◇ q0) = q1:=by
    intro q0 q1
    exact ((congrArg (fun t => ((q1 ◇ q1) ◇ (q0 ◇ q0)) ◇ t) ((h q0 q1 q1).symm)).symm).trans ((h q1 (q1 ◇ q1) (q0 ◇ q0)).symm)
  have apc1 : forall (q2:G), (q2 ◇ (q2 ◇ q2)) = q2:=by
    intro q2
    exact ((congrArg (fun t => t ◇ (q2 ◇ q2)) ((h q2 q2 q2).symm)).symm).trans (apc0 (q2 ◇ q2) q2)
  have apc2 : forall (q3:G), (q3 ◇ q3) = q3:=by
    intro q3
    exact ((apc1 (q3 ◇ q3)).symm).trans ((h q3 q3 q3).symm)
  have apc3 : forall (q4 q5:G), (q5 ◇ (q4 ◇ q5)) = q4:=by
    intro q4 q5
    exact (((congrArg (fun t => q5 ◇ t) (congrArg (fun t => t ◇ (q5 ◇ q5)) (apc2 q4))).trans (congrArg (fun t => q5 ◇ t) (congrArg (fun t => q4 ◇ t) (apc2 q5)))).symm).trans (((congrArg (fun t => t ◇ ((q4 ◇ q4) ◇ (q5 ◇ q5))) (apc2 q5)).symm).trans ((h q4 q5 q5).symm))
  have apc5 : forall (q6 q7 q8:G), (q6 ◇ (q7 ◇ ((q6 ◇ q8) ◇ q8))) = q7:=by
    intro q6 q7 q8
    exact ((congrArg (fun t => q6 ◇ t) (congrArg (fun t => t ◇ ((q6 ◇ q8) ◇ q8)) (apc2 q7))).symm).trans (((congrArg (fun t => t ◇ ((q7 ◇ q7) ◇ ((q6 ◇ q8) ◇ q8))) (apc3 q6 q8)).symm).trans ((h q7 q8 (q6 ◇ q8)).symm))
  have apc11 : forall (q9 q10:G), (q9 ◇ (q9 ◇ q10)) = q10:=by
    intro q9 q10
    exact ((congrArg (fun t => q9 ◇ t) (apc3 (q9 ◇ q10) q10)).symm).trans (apc5 q9 q10 q10)
  exact (calc
    x = x:=rfl
    _ = (y ◇ (y ◇ (x ◇ (z ◇ (x ◇ z))))):=(((congrArg (fun t => y ◇ t) (congrArg (fun t => y ◇ t) (congrArg (fun t => x ◇ t) (apc3 x z)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => y ◇ t) (apc2 x)))).trans (apc11 y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19241_to_5071 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19241_to_5071
