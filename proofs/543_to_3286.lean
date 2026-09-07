-- Equation543 → Equation3286
-- Recorded verdict: true
-- Premise: x = y ◇ (z ◇ (x ◇ (y ◇ z)))
-- Conclusion: x ◇ x = y ◇ (y ◇ (z ◇ z))
-- Original submission SHA-256: aab8ac9fbe19634d5f2ff15886849dfd50080dcfbda83eb59ad85ac38fffc93f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ (x ◇ (y ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (y ◇ (z ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc2 : forall (q0 q1 q2:G), (q2 ◇ ((q0 ◇ (q1 ◇ q2)) ◇ q0)) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => (q0 ◇ (q1 ◇ q2)) ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h q1 q2 (q0 ◇ (q1 ◇ q2))).symm)
  have apc3 : forall (q3 q4 q5:G), ((q4 ◇ q5) ◇ (q3 ◇ q5)) = (q4 ◇ q3):=by
    intro q3 q4 q5
    exact (((congrArg (fun t => q4 ◇ t) (apc2 (q4 ◇ q5) q3 q5)).symm).trans ((h ((q4 ◇ q5) ◇ (q3 ◇ q5)) q4 q5).symm)).symm
  have apc4 : forall (q6 q7 q8:G), (q7 ◇ (q8 ◇ (q6 ◇ q7))) = (q6 ◇ q8):=by
    intro q6 q7 q8
    exact ((congrArg (fun t => q7 ◇ t) (congrArg (fun t => q8 ◇ t) (apc3 q7 q6 q8))).symm).trans ((h (q6 ◇ q8) q7 q8).symm)
  have apc5 : forall (q9 q10:G), (q10 ◇ (q10 ◇ q9)) = q9:=by
    intro q9 q10
    exact ((congrArg (fun t => q10 ◇ t) (apc4 q10 q9 q9)).symm).trans ((h q9 q10 q9).symm)
  exact (((apc5 (x ◇ x) y).symm).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => y ◇ t) ((apc4 x z x).symm)))).trans ((congrArg (fun t => y ◇ t) (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) ((apc5 z x).symm)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_543_to_3286 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_543_to_3286
