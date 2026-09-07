-- Equation11017 → Equation61938
-- Recorded verdict: true
-- Premise: x = x * ((y * (z * w)) * (y * y))
-- Conclusion: (x * y) * x = ((x * z) * w) * w
-- Original submission SHA-256: f3ef2e0761eef92086c9bb68ced1d65f90634467a94165041d46d93f286475fa
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ ((y ◇ (z ◇ w)) ◇ (y ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ x = ((x ◇ z) ◇ w) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), (q0 ◇ (q1 ◇ (q1 ◇ q1))) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => q0 ◇ t) (congrArg (fun t => t ◇ (q1 ◇ q1)) ((h q1 q0 q0 q0).symm))).symm).trans ((h q0 q1 (q0 ◇ (q0 ◇ q0)) (q0 ◇ q0)).symm)
  have apc1 : forall (q0 q1 q2:G), (q0 ◇ ((q1 ◇ q2) ◇ (q1 ◇ q1))) = q0:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q0 ◇ t) (congrArg (fun t => t ◇ (q1 ◇ q1)) (congrArg (fun t => q1 ◇ t) ((h q2 q0 q0 q0).symm)))).symm).trans ((h q0 q1 q2 ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0))).symm)
  have apc2 : forall (q3 q4:G), (q4 ◇ (q3 ◇ q3)) = q4:=by
    intro q3 q4
    exact ((congrArg (fun t => q4 ◇ t) (apc1 (q3 ◇ q3) q3 q3)).symm).trans (apc0 q4 (q3 ◇ q3))
  have apc3 : forall (q0 q1 q3 q4:G), (q0 ◇ q1) = q0:=by
    intro q0 q1 q3 q4
    exact ((congrArg (fun t => q0 ◇ t) (apc2 q1 q1)).symm).trans (apc0 q0 q1)
  exact (calc
    ((x ◇ y) ◇ x) = x:=(congrArg (fun t => t ◇ x) (apc3 x y (x ◇ y) (x ◇ y))).trans (apc3 x x (x ◇ x) (x ◇ x))
    _ = (((x ◇ z) ◇ w) ◇ w):=(((congrArg (fun t => t ◇ w) (congrArg (fun t => t ◇ w) (apc3 x z (x ◇ z) (x ◇ z)))).trans (congrArg (fun t => t ◇ w) (apc3 x w (x ◇ w) (x ◇ w)))).trans (apc3 x w (x ◇ w) (x ◇ w))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_11017_to_61938 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_11017_to_61938
