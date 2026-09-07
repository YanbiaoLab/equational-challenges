-- Equation15361 → Equation38188
-- Recorded verdict: true
-- Premise: x = x * (((y * (z * x)) * w) * u)
-- Conclusion: x = ((x * ((y * z) * z)) * y) * w
-- Original submission SHA-256: 31e4325013c0caa29fc36bf111674450eeebabee8c8ffd38e9e3d5b0a600b592
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = x ◇ (((y ◇ (z ◇ x)) ◇ w) ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((x ◇ ((y ◇ z) ◇ z)) ◇ y) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ ((q3 ◇ q1) ◇ q0)) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ q0) (congrArg (fun t => t ◇ q1) ((h q3 q0 q0 q0 q2).symm)))).symm).trans ((h q2 q3 ((q0 ◇ (q0 ◇ q3)) ◇ q0) q1 q0).symm)
  have apc1 : forall (q4 q5 q6:G), (q5 ◇ (q6 ◇ q4)) = q5:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => q5 ◇ t) (apc0 q4 q4 (q6 ◇ q4) q4)).symm).trans (apc0 ((q4 ◇ q4) ◇ q4) q4 q5 q6)
  have apc2 : forall (q7 q8:G), (q7 ◇ q8) = q7:=by
    intro q7 q8
    exact ((congrArg (fun t => q7 ◇ t) (apc1 q7 q8 q7)).symm).trans (apc1 (q7 ◇ q7) q7 q8)
  exact (calc
    x = x:=rfl
    _ = (((x ◇ ((y ◇ z) ◇ z)) ◇ y) ◇ w):=(((((congrArg (fun t => t ◇ w) (congrArg (fun t => t ◇ y) (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ z) (apc2 y z))))).trans (congrArg (fun t => t ◇ w) (congrArg (fun t => t ◇ y) (congrArg (fun t => x ◇ t) (apc2 y z))))).trans (congrArg (fun t => t ◇ w) (congrArg (fun t => t ◇ y) (apc2 x y)))).trans (congrArg (fun t => t ◇ w) (apc2 x y))).trans (apc2 x w)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_15361_to_38188 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_15361_to_38188
