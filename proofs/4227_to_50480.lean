-- Equation4227 → Equation50480
-- Recorded verdict: true
-- Premise: x * y = ((z * z) * x) * z
-- Conclusion: x * x = (y * ((z * w) * x)) * u
-- Original submission SHA-256: bb8c2873c93c414a3ceec3ae179c4c93f45b7590b0882f0aa21c90d0e825dad0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ z) ◇ x) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ x = (y ◇ ((z ◇ w) ◇ x)) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc1 : forall (q0 q1 q2 q3:G), (((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2 q3
    exact (((apc0 q0 q2 (q0 ◇ q2)).symm).trans (((h q0 q2 q3).trans (h ((q3 ◇ q3) ◇ q0) q3 q1)).trans (congrArg (fun t => t ◇ q1) (apc0 (q1 ◇ q1) ((q3 ◇ q3) ◇ q0) ((q1 ◇ q1) ◇ ((q3 ◇ q3) ◇ q0)))))).symm
  have apc3 : forall (q0 q2 q3 q1:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q2 q3 q1
    exact (((apc1 q0 q1 q2 q3).symm).trans (apc1 q1 q1 q2 q3)).symm
  exact (calc
    (x ◇ x) = ((y ◇ ((z ◇ w) ◇ x)) ◇ (y ◇ ((z ◇ w) ◇ x))):=apc3 (y ◇ ((z ◇ w) ◇ x)) u u x
    _ = ((y ◇ ((z ◇ w) ◇ x)) ◇ u):=(apc0 (y ◇ ((z ◇ w) ◇ x)) u u).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4227_to_50480 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4227_to_50480
