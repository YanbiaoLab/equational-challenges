-- Equation58178 → Equation56579
-- Recorded verdict: true
-- Premise: x * (y * z) = ((w * u) * w) * v
-- Conclusion: x * (x * y) = (z * (x * w)) * w
-- Original submission SHA-256: 4e16cdae405f74ef8edf14cf5fb019d5053d6f1b664fa55e77ea4d38b4de918c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ (y ◇ z) = ((w ◇ u) ◇ w) ◇ v
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = (z ◇ (x ◇ w)) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3 q4 q5 q6 : G), ((q0 ◇ (q1 ◇ q2)) ◇ q3) = (q4 ◇ (q5 ◇ q6)) := by
    intro q0 q1 q2 q3 q4 q5 q6
    exact ((rfl).symm).trans ((((congrArg (fun t => t ◇ q3) ((h q0 q1 q2 q0 q0 (q0 ◇ q0)).symm)).symm).trans ((h q4 q5 q6 (q0 ◇ q0) q0 q3).symm)).trans (rfl))
  have apc11 : forall (x y z w u v : G), (x ◇ (y ◇ z)) = (w ◇ (w ◇ w)) := by
    intro x y z w u v
    exact ((rfl).symm).trans (((h x y z w u v).trans ((h w w w w u v).symm)).trans (rfl))
  have apc12 : forall (q7 q8 q9 q10 q11 : G), ((q8 ◇ (q9 ◇ q10)) ◇ q11) = (q7 ◇ (q7 ◇ q7)) := by
    intro q7 q8 q9 q10 q11
    exact (((rfl).symm).trans ((((apc11 q7 q7 q7 q7 q7 q7).symm).trans ((apc0 q8 q9 q10 q11 q7 q7 q7).symm)).trans (rfl))).symm
  exact (calc
    (x ◇ (x ◇ y)) = (w ◇ (w ◇ w)) := apc11 x x y w w w
    _ = ((z ◇ (x ◇ w)) ◇ w) := (apc12 w z x w w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_58178_to_56579 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_58178_to_56579
