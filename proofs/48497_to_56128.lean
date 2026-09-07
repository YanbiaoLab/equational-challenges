-- Equation48497 → Equation56128
-- Recorded verdict: true
-- Premise: x * y = (z * (w * w)) * (w * x)
-- Conclusion: x * (y * z) = (x * w) * (z * y)
-- Original submission SHA-256: a922747a997194c9cb321a64a25145e3af8bc51a0072d748d57a6e143e8f900f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (w ◇ w)) ◇ (w ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (x ◇ w) ◇ (z ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc1 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc5 : forall (x z w y:G), ((z ◇ z) ◇ (w ◇ w)) = ((x ◇ x) ◇ (x ◇ x)):=by
    intro x z w y
    exact (((congrArg (fun t => (z ◇ (w ◇ w)) ◇ t) (apc1 w x (w ◇ x) (w ◇ x))).trans (congrArg (fun t => t ◇ (w ◇ w)) (apc1 z (w ◇ w) (z ◇ (w ◇ w)) (z ◇ (w ◇ w))))).symm).trans ((((h x y z w).symm).trans (h x y x x)).trans (congrArg (fun t => t ◇ (x ◇ x)) (apc1 x (x ◇ x) (x ◇ (x ◇ x)) (x ◇ (x ◇ x)))))
  have apc6 : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ (q2 ◇ q2)) = (q1 ◇ q0):=by
    intro q0 q1 q2
    exact ((h q1 q0 (q1 ◇ q1) q1).trans (apc5 q2 (q1 ◇ q1) q1 q0)).symm
  exact ((apc6 (y ◇ z) x (x ◇ (y ◇ z))).symm).trans (apc6 (z ◇ y) (x ◇ w) (x ◇ (y ◇ z)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48497_to_56128 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48497_to_56128
