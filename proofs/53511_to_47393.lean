-- Equation53511 → Equation47393
-- Recorded verdict: true
-- Premise: x * y = (((z * x) * w) * u) * v
-- Conclusion: x * y = (z * y) * ((y * x) * w)
-- Original submission SHA-256: e2d0b981ce3c27797b11f83779dc60ce7f3686f9307787da2b3a11ab361c2a04
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = (((z ◇ x) ◇ w) ◇ u) ◇ v
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ y) ◇ ((y ◇ x) ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u v:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u v
    exact (h x y x x x x).trans ((h x x x x x x).symm)
  have apc24 : forall (q0 q1 q2 q3 q4:G), ((((q0 ◇ q0) ◇ q3) ◇ q1) ◇ q2) = (q4 ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ q2) (congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q3) (apc0 q0 q0 (q0 ◇ q0) (q0 ◇ q0) (q0 ◇ q0) (q0 ◇ q0))))).symm).trans ((((congrArg (fun t => t ◇ q2) (congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q3) ((h q0 q0 q0 q0 q0 q4).symm)))).symm).trans ((h q4 q0 (((q0 ◇ q0) ◇ q0) ◇ q0) q3 q1 q2).symm)).trans (apc0 q4 q0 (q4 ◇ q0) (q4 ◇ q0) (q4 ◇ q0) (q4 ◇ q0)))
  have apc25 : forall (q5 q6 q7:G), (q7 ◇ q7) = (q6 ◇ q5):=by
    intro q5 q6 q7
    exact ((h q6 q5 q6 q5 q5 q5).trans (apc24 q6 q5 q5 q5 q7)).symm
  exact ((apc25 y x (x ◇ y)).symm).trans (apc25 ((y ◇ x) ◇ w) (z ◇ y) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53511_to_47393 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53511_to_47393
