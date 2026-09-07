-- Equation2009 → Equation13829
-- Recorded verdict: true
-- Premise: x = (y * (z * w)) * (x * x)
-- Conclusion: x = y * ((y * ((x * y) * x)) * x)
-- Original submission SHA-256: 8c65d8a7321e20986cded26ae5f6f27f17d2ad0c93c52e4d269bfb4ddfeb80a6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ w)) ◇ (x ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ ((y ◇ ((x ◇ y) ◇ x)) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1:G), (q0 ◇ (q1 ◇ q1)) = q1:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ (q1 ◇ q1)) ((h q0 q0 q0 q0).symm)).symm).trans ((h q1 (q0 ◇ (q0 ◇ q0)) q0 q0).symm)
  have apc1 : forall (q2 q3:G), (q3 ◇ q2) = (q2 ◇ q2):=by
    intro q2 q3
    exact ((congrArg (fun t => q3 ◇ t) (apc0 (q2 ◇ q2) q2)).symm).trans (apc0 q3 (q2 ◇ q2))
  exact (calc
    x = x:=rfl
    _ = (y ◇ ((y ◇ ((x ◇ y) ◇ x)) ◇ x)):=(((congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ x) (congrArg (fun t => y ◇ t) (apc1 x (x ◇ y))))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ x) (apc0 y x)))).trans (apc0 y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_2009_to_13829 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_2009_to_13829
