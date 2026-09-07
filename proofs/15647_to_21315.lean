-- Equation15647 → Equation21315
-- Recorded verdict: true
-- Premise: x = y * (((y * (z * x)) * x) * x)
-- Conclusion: x = (y * z) * (((w * w) * u) * x)
-- Original submission SHA-256: 86102173973e7e4cba30594fd7b356010646a144d5f57391887675dc992752ce
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (((y ◇ (z ◇ x)) ◇ x) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ z) ◇ (((w ◇ w) ◇ u) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q0) ◇ q0)) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => q1 ◇ t) (congrArg (fun t => t ◇ q0) (congrArg (fun t => t ◇ q0) ((h q0 q1 q0).symm)))).symm).trans ((h q0 q1 ((q1 ◇ (q0 ◇ q0)) ◇ q0)).symm)
  have apc1 : forall (q2 q3:G), ((q2 ◇ q2) ◇ q2) = (q3 ◇ q2):=by
    intro q2 q3
    exact (((congrArg (fun t => q3 ◇ t) (apc0 q2 ((q3 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ q2) ◇ q2)))).symm).trans ((h ((q2 ◇ q2) ◇ q2) q3 q2).symm)).symm
  have apc4 : forall (q4 q5 q6:G), (q6 ◇ (q4 ◇ q5)) = q5:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => q6 ◇ t) (apc1 q5 q4)).symm).trans (apc0 q5 q6)
  exact (calc
    x = x:=rfl
    _ = ((y ◇ z) ◇ (((w ◇ w) ◇ u) ◇ x)):=(apc4 ((w ◇ w) ◇ u) x (y ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_15647_to_21315 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_15647_to_21315
