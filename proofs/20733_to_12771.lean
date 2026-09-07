-- Equation20733 → Equation12771
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ (((y ◇ y) ◇ x) ◇ z)
-- Conclusion: x = x ◇ ((y ◇ (z ◇ (w ◇ y))) ◇ y)
-- Original submission SHA-256: 0bb0e4190f301f97855f8599595d1a5bed957c4b7943bb5e202473084f09b6de
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ (((y ◇ y) ◇ x) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ ((y ◇ (z ◇ (w ◇ y))) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), ((q1 ◇ q0) ◇ q0) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => (q1 ◇ q0) ◇ t) ((h q0 (q1 ◇ q1) q0).symm)).symm).trans ((h q0 q1 ((((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q2:G), (q2 ◇ q2) = q2:=by
    intro q2
    exact ((congrArg (fun t => t ◇ q2) (apc0 q2 q2)).symm).trans (apc0 q2 (q2 ◇ q2))
  have apc3 : forall (q3 q4:G), (q4 ◇ q3) = q3:=by
    intro q3 q4
    exact (((congrArg (fun t => (q4 ◇ q3) ◇ t) (congrArg (fun t => t ◇ q3) (apc1 q4))).trans (apc1 (q4 ◇ q3))).symm).trans (((congrArg (fun t => (q4 ◇ q3) ◇ t) (apc1 ((q4 ◇ q4) ◇ q3))).symm).trans ((h q3 q4 ((q4 ◇ q4) ◇ q3)).symm))
  have apc4 : forall (x y z:G), z = x:=by
    intro x y z
    exact ((((((congrArg (fun t => (y ◇ x) ◇ t) (congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ x) (apc3 y y)))).trans (congrArg (fun t => (y ◇ x) ◇ t) (congrArg (fun t => t ◇ z) (apc3 x y)))).trans (congrArg (fun t => (y ◇ x) ◇ t) (apc3 z x))).trans (congrArg (fun t => t ◇ z) (apc3 x y))).trans (apc3 z x)).symm).trans ((((h x y z).symm).trans (h x x x)).trans (((((congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ x) (apc3 x x)))).trans (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => t ◇ x) (apc3 x x)))).trans (congrArg (fun t => t ◇ (x ◇ x)) (apc3 x x))).trans (congrArg (fun t => x ◇ t) (apc3 x x))).trans (apc3 x x)))
  exact (apc4 x x x).trans ((apc4 x x (x ◇ ((y ◇ (z ◇ (w ◇ y))) ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_20733_to_12771 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_20733_to_12771
