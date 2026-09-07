-- Equation1896 → Equation23251
-- Recorded verdict: true
-- Premise: x = (y ◇ (x ◇ y)) ◇ (x ◇ z)
-- Conclusion: x = ((x ◇ y) ◇ z) ◇ (x ◇ (w ◇ y))
-- Original submission SHA-256: 06498ce2b9a3d35b3e133bf06c83d8c720b71523203b3d805752b98538de515b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ y)) ◇ (x ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((x ◇ y) ◇ z) ◇ (x ◇ (w ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), (q0 ◇ (q0 ◇ q1)) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ (q0 ◇ q1)) ((h q0 q0 (q0 ◇ (q0 ◇ q0))).symm)).symm).trans ((h q0 (q0 ◇ (q0 ◇ q0)) q1).symm)
  have apc1 : forall (q2 q3 q4:G), (((q3 ◇ q2) ◇ q3) ◇ (q3 ◇ q4)) = q3:=by
    intro q2 q3 q4
    exact ((congrArg (fun t => t ◇ (q3 ◇ q4)) (congrArg (fun t => (q3 ◇ q2) ◇ t) (apc0 q3 q2))).symm).trans ((h q3 (q3 ◇ q2) q4).symm)
  have apc2 : forall (q5 q6:G), (((q6 ◇ q5) ◇ q6) ◇ q6) = q6:=by
    intro q5 q6
    exact ((congrArg (fun t => ((q6 ◇ q5) ◇ q6) ◇ t) (apc0 q6 q5)).symm).trans (apc1 q5 q6 (q6 ◇ q5))
  have apc6 : forall (q7 q8:G), (q8 ◇ q7) = q8:=by
    intro q7 q8
    exact (((apc0 q8 q7).symm).trans (((congrArg (fun t => t ◇ (q8 ◇ q7)) (apc1 q7 q8 q7)).symm).trans (apc2 q8 (q8 ◇ q7)))).symm
  have apc7 : forall (q9 q10:G), q10 = q9:=by
    intro q9 q10
    exact (((congrArg (fun t => q10 ◇ t) (apc6 q10 q9)).trans (apc6 q9 q10)).symm).trans (((apc6 (q9 ◇ q9) (q10 ◇ (q9 ◇ q10))).symm).trans ((h q9 q10 q9).symm))
  exact (apc7 x x).trans ((apc7 x (((x ◇ y) ◇ z) ◇ (x ◇ (w ◇ y)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1896_to_23251 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_1896_to_23251
