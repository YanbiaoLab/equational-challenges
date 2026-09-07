-- Equation24215 → Equation39037
-- Recorded verdict: true
-- Premise: x = ((y ◇ x) ◇ x) ◇ ((z ◇ x) ◇ w)
-- Conclusion: x = (((x ◇ y) ◇ (z ◇ x)) ◇ w) ◇ y
-- Original submission SHA-256: b62df7dc4f9f0bd756f0e3d64c3d973f46d22e29ff1770e64444e6f487836f39
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ x) ◇ x) ◇ ((z ◇ x) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (((x ◇ y) ◇ (z ◇ x)) ◇ w) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), (((q1 ◇ q0) ◇ q0) ◇ q0) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => ((q1 ◇ q0) ◇ q0) ◇ t) ((h q0 q0 q0 q0).symm)).symm).trans ((h q0 q1 (q0 ◇ q0) ((q0 ◇ q0) ◇ q0)).symm)
  have apc2 : forall (q2:G), (q2 ◇ q2) = q2:=by
    intro q2
    exact ((congrArg (fun t => t ◇ q2) (apc0 q2 q2)).symm).trans (apc0 q2 (q2 ◇ q2))
  have apc3 : forall (q3 q4:G), ((q4 ◇ q3) ◇ q3) = q3:=by
    intro q3 q4
    exact ((apc2 ((q4 ◇ q3) ◇ q3)).symm).trans ((h q3 q4 q4 q3).symm)
  have apc4 : forall (q5 q6 q7:G), (q6 ◇ (q6 ◇ q5)) = q6:=by
    intro q5 q6 q7
    exact ((congrArg (fun t => t ◇ (q6 ◇ q5)) (apc3 q6 q7)).symm).trans (((congrArg (fun t => ((q7 ◇ q6) ◇ q6) ◇ t) (congrArg (fun t => t ◇ q5) (apc0 q6 q5))).symm).trans ((h q6 q7 ((q5 ◇ q6) ◇ q6) q5).symm))
  have apc7 : forall (q8 q9:G), (q9 ◇ q8) = q9:=by
    intro q8 q9
    exact (((apc4 q8 q9 (q9 ◇ (q9 ◇ q8))).symm).trans (((congrArg (fun t => t ◇ (q9 ◇ q8)) (apc4 q8 q9 q8)).symm).trans (apc3 (q9 ◇ q8) q9))).symm
  exact (calc
    x = x:=rfl
    _ = ((((x ◇ y) ◇ (z ◇ x)) ◇ w) ◇ y):=(((((congrArg (fun t => t ◇ y) (congrArg (fun t => t ◇ w) (congrArg (fun t => t ◇ (z ◇ x)) (apc7 y x)))).trans (congrArg (fun t => t ◇ y) (congrArg (fun t => t ◇ w) (congrArg (fun t => x ◇ t) (apc7 x z))))).trans (congrArg (fun t => t ◇ y) (congrArg (fun t => t ◇ w) (apc7 z x)))).trans (congrArg (fun t => t ◇ y) (apc7 w x))).trans (apc7 y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_24215_to_39037 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_24215_to_39037
