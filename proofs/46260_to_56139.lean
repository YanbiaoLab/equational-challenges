-- Equation46260 → Equation56139
-- Recorded verdict: true
-- Premise: x * y = (x * z) * (w * (w * w))
-- Conclusion: x * (y * z) = (x * w) * (u * z)
-- Original submission SHA-256: f55e132aaa3e7f9c04ccddb45e575ec1d169fbc511cc8777c12ef29c973d95d1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (x ◇ z) ◇ (w ◇ (w ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = (x ◇ w) ◇ (u ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2:G), ((q2 ◇ q1) ◇ (q0 ◇ q0)) = (q2 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q2 ◇ q1) ◇ t) (apc0 q0 (q0 ◇ q0) (q0 ◇ (q0 ◇ q0)) (q0 ◇ (q0 ◇ q0)))).symm).trans (((h q2 q0 q1 q0).symm).trans (apc0 q2 q0 q0 q0))
  exact (calc
    (x ◇ (y ◇ z)) = (x ◇ x):=(congrArg (fun t => x ◇ t) (apc0 y z (y ◇ z) (y ◇ z))).trans (apc0 x (y ◇ y) (x ◇ (y ◇ y)) (x ◇ (y ◇ y)))
    _ = ((x ◇ w) ◇ (u ◇ z)):=((congrArg (fun t => (x ◇ w) ◇ t) (apc0 u z (u ◇ z) (u ◇ z))).trans (apc1 u w x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46260_to_56139 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46260_to_56139
