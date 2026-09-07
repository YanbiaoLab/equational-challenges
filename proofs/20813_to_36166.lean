-- Equation20813 → Equation36166
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ (((z ◇ w) ◇ x) ◇ u)
-- Conclusion: x = ((y ◇ (z ◇ w)) ◇ (y ◇ z)) ◇ u
-- Original submission SHA-256: 44ae9999d7299e5fe4d12567b96086b259567cc8ad3c0c1494f6d537b67965eb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ x) ◇ (((z ◇ w) ◇ x) ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((y ◇ (z ◇ w)) ◇ (y ◇ z)) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1:G), ((q1 ◇ q0) ◇ q0) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => (q1 ◇ q0) ◇ t) ((h q0 (q0 ◇ q0) q0 q0 q0).symm)).symm).trans ((h q0 q1 q0 q0 (((q0 ◇ q0) ◇ q0) ◇ q0)).symm)
  have apc2 : forall (q2 q3 q4:G), ((q4 ◇ q3) ◇ (q3 ◇ q2)) = q3:=by
    intro q2 q3 q4
    exact ((congrArg (fun t => (q4 ◇ q3) ◇ t) (congrArg (fun t => t ◇ q2) (apc0 q3 q2))).symm).trans ((h q3 q4 q2 q3 q2).symm)
  have apc3 : forall (q5 q6 q7:G), ((q7 ◇ (q5 ◇ q6)) ◇ q6) = (q5 ◇ q6):=by
    intro q5 q6 q7
    exact ((congrArg (fun t => (q7 ◇ (q5 ◇ q6)) ◇ t) (apc0 q6 q5)).symm).trans (apc2 q6 (q5 ◇ q6) q7)
  have apc4 : forall (q8 q9:G), (q8 ◇ q9) = q9:=by
    intro q8 q9
    exact (((apc0 q9 q8).symm).trans (((congrArg (fun t => t ◇ q9) (apc0 (q8 ◇ q9) q8)).symm).trans (apc3 q8 q9 (q8 ◇ (q8 ◇ q9))))).symm
  have apc5 : forall (x y z w u:G), x = u:=by
    intro x y z w u
    exact (((((((congrArg (fun t => (y ◇ x) ◇ t) (congrArg (fun t => t ◇ u) (congrArg (fun t => t ◇ x) (apc4 z w)))).trans (congrArg (fun t => (y ◇ x) ◇ t) (congrArg (fun t => t ◇ u) (apc4 w x)))).trans (congrArg (fun t => (y ◇ x) ◇ t) (apc4 x u))).trans (congrArg (fun t => t ◇ u) (apc4 y x))).trans (apc4 x u)).symm).trans ((((h x y z w u).symm).trans (h x x x x x)).trans (((((congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ x) (apc4 x x)))).trans (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => t ◇ x) (apc4 x x)))).trans (congrArg (fun t => t ◇ (x ◇ x)) (apc4 x x))).trans (congrArg (fun t => x ◇ t) (apc4 x x))).trans (apc4 x x)))).symm
  exact (apc5 x x x x x).trans ((apc5 (((y ◇ (z ◇ w)) ◇ (y ◇ z)) ◇ u) x x x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_20813_to_36166 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_20813_to_36166
