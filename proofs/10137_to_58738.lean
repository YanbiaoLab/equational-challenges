-- Equation10137 → Equation58738
-- Recorded verdict: true
-- Premise: x = x * ((y * z) * ((w * x) * w))
-- Conclusion: (x * y) * z = x * (z * (y * w))
-- Original submission SHA-256: d2e449fad20b023a4c98fe645a2680030b7a504d803b874da14f6995c9389d37
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ ((y ◇ z) ◇ ((w ◇ x) ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = x ◇ (z ◇ (y ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q0 ◇ (q1 ◇ q2)) = q0:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q0 ◇ t) ((h (q1 ◇ q2) ((q0 ◇ (q1 ◇ q2)) ◇ q0) q0 q0).symm)).symm).trans ((h q0 q1 q2 ((q0 ◇ (q1 ◇ q2)) ◇ q0)).symm)
  have apc1 : forall (q0 q1 q3:G), (q0 ◇ q1) = q0:=by
    intro q0 q1 q3
    exact ((congrArg (fun t => q0 ◇ t) (apc0 q1 (q3 ◇ q0) q3)).symm).trans (((congrArg (fun t => q0 ◇ t) (congrArg (fun t => t ◇ ((q3 ◇ q0) ◇ q3)) ((h q1 q3 q3 q3).symm))).symm).trans ((h q0 q1 ((q3 ◇ q3) ◇ ((q3 ◇ q1) ◇ q3)) q3).symm))
  exact (calc
    ((x ◇ y) ◇ z) = x:=(congrArg (fun t => t ◇ z) (apc1 x y (x ◇ y))).trans (apc1 x z (x ◇ z))
    _ = (x ◇ (z ◇ (y ◇ w))):=(((congrArg (fun t => x ◇ t) (congrArg (fun t => z ◇ t) (apc1 y w (y ◇ w)))).trans (congrArg (fun t => x ◇ t) (apc1 z y (z ◇ y)))).trans (apc1 x z (x ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_10137_to_58738 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_10137_to_58738
