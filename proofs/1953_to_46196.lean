-- Equation1953 → Equation46196
-- Recorded verdict: true
-- Premise: x = (y * (y * z)) * (w * x)
-- Conclusion: x * y = (x * z) * (x * (y * y))
-- Original submission SHA-256: 6b62a913adce391bae0d093402c679044ca2d018724a32dc507bfc1018257566
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (y ◇ z)) ◇ (w ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (x ◇ z) ◇ (x ◇ (y ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), ((q2 ◇ (q2 ◇ q3)) ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => (q2 ◇ (q2 ◇ q3)) ◇ t) ((h q1 q0 q0 q0).symm)).symm).trans ((h (q0 ◇ q1) q2 q3 (q0 ◇ (q0 ◇ q0))).symm)
  have apc1 : forall (q0 q1 q2 q3:G), (q1 ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1 q2 q3
    exact (((apc0 q0 q1 q2 q3).symm).trans (apc0 q1 q1 q2 q3)).symm
  have apc2 : forall (q4 q5 q6:G), (q4 ◇ (q5 ◇ (q5 ◇ q6))) = (q5 ◇ q6):=by
    intro q4 q5 q6
    exact ((apc1 q4 (q5 ◇ (q5 ◇ q6)) q4 q4).symm).trans ((h (q5 ◇ q6) q5 q6 q5).symm)
  have apc3 : forall (q7 q8 q9:G), (q7 ◇ (q8 ◇ (q9 ◇ q9))) = (q8 ◇ q9):=by
    intro q7 q8 q9
    exact ((congrArg (fun t => q7 ◇ t) (congrArg (fun t => q8 ◇ t) ((apc1 q8 q9 q7 q7).symm))).symm).trans (apc2 q7 q8 q9)
  exact (apc3 (x ◇ z) x y).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1953_to_46196 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_1953_to_46196
