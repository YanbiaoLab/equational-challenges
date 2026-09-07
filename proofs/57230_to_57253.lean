-- Equation57230 → Equation57253
-- Recorded verdict: true
-- Premise: x * (y * z) = (w * (z * x)) * u
-- Conclusion: x * (y * z) = (w * (w * x)) * y
-- Original submission SHA-256: 3d8097ec5475680dfee569d9862214c1079a121dbfbde27fd7ddf3cdbcd157be
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = (w ◇ (z ◇ x)) ◇ u
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (w ◇ (w ◇ x)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u:G), (x ◇ (y ◇ z)) = (x ◇ (x ◇ z)):=by
    intro x y z w u
    exact (h x y z x x).trans ((h x x z x x).symm)
  have apc13 : forall (x y z w u:G), ((w ◇ (w ◇ x)) ◇ u) = (x ◇ (x ◇ z)):=by
    intro x y z w u
    exact (((apc0 x x z (x ◇ (x ◇ z)) (x ◇ (x ◇ z))).symm).trans ((h x x z w u).trans (congrArg (fun t => t ◇ u) (apc0 w z x (w ◇ (z ◇ x)) (w ◇ (z ◇ x)))))).symm
  have apc14 : forall (q0 q1 q2 q3:G), (q2 ◇ (q2 ◇ q3)) = (q2 ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact ((h q2 q0 q1 q1 q0).trans (apc13 q2 q0 q3 q1 q0)).symm
  have apc16 : forall (q4 q5 q6 q7 q8:G), (q8 ◇ (q6 ◇ q7)) = (q8 ◇ (q4 ◇ q5)):=by
    intro q4 q5 q6 q7 q8
    exact (((apc14 q4 q5 q8 q4).symm).trans (apc14 q6 q7 q8 q4)).symm
  exact (calc
    (x ◇ (y ◇ z)) = (x ◇ (y ◇ w)):=apc16 y w y z x
    _ = ((w ◇ (w ◇ x)) ◇ y):=((h x y w w y).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_57230_to_57253 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_57230_to_57253
