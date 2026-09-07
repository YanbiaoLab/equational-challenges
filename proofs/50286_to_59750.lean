-- Equation50286 → Equation59750
-- Recorded verdict: true
-- Premise: x * y = (z * (w * (u * u))) * x
-- Conclusion: (x * y) * z = z * ((y * y) * y)
-- Original submission SHA-256: d18c4d4ae0ef76cf11c6d48e3c84b2a8ab081cf86d9ea023121dfd4ea7427eca
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ (w ◇ (u ◇ u))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = z ◇ ((y ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ q0) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => t ◇ q0) (apc0 q1 (q0 ◇ (q0 ◇ q0)) q0 q0 q0)).symm).trans ((h q0 q2 q1 q0 q0).symm)).trans (apc0 q0 q2 (q0 ◇ q2) (q0 ◇ q2) (q0 ◇ q2))
  exact (calc
    ((x ◇ y) ◇ z) = (z ◇ z):=(congrArg (fun t => t ◇ z) (apc0 x y (x ◇ y) (x ◇ y) (x ◇ y))).trans (apc1 z x ((x ◇ x) ◇ z))
    _ = (z ◇ ((y ◇ y) ◇ y)):=((congrArg (fun t => z ◇ t) (apc1 y y ((y ◇ y) ◇ y))).trans (apc0 z (y ◇ y) (z ◇ (y ◇ y)) (z ◇ (y ◇ y)) (z ◇ (y ◇ y)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50286_to_59750 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_50286_to_59750
