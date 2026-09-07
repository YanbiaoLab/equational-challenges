-- Equation20083 → Equation7319
-- Recorded verdict: true
-- Premise: x = (y * y) * ((z * (w * x)) * x)
-- Conclusion: x = y * (z * ((w * u) * (v * x)))
-- Original submission SHA-256: 16aebc135694dfebe3d36e8f88cc0f33e8fd1497b98635b16fb3232b5b523909
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ y) ◇ ((z ◇ (w ◇ x)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x = y ◇ (z ◇ ((w ◇ u) ◇ (v ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have apc0 : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q0 ◇ q0)) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => (q1 ◇ q1) ◇ t) (congrArg (fun t => t ◇ q0) ((h q0 q0 q0 q0).symm))).symm).trans ((h q0 q1 (q0 ◇ q0) (q0 ◇ (q0 ◇ q0))).symm)
  have apc1 : forall (q2 q3:G), (q2 ◇ (q3 ◇ q3)) = q3:=by
    intro q2 q3
    exact ((congrArg (fun t => t ◇ (q3 ◇ q3)) (apc0 q2 q2)).symm).trans (apc0 q3 (q2 ◇ q2))
  have apc2 : forall (q4 q5:G), (q5 ◇ q4) = (q4 ◇ q4):=by
    intro q4 q5
    exact ((congrArg (fun t => q5 ◇ t) (apc1 (q4 ◇ q4) q4)).symm).trans (apc1 q5 (q4 ◇ q4))
  exact (calc
    x = (y ◇ (x ◇ x)):=(apc1 y x).symm
    _ = (y ◇ (v ◇ x)):=congrArg (fun t => y ◇ t) ((apc2 x v).symm)
    _ = (y ◇ (z ◇ ((v ◇ x) ◇ (v ◇ x)))):=(congrArg (fun t => y ◇ t) (apc1 z (v ◇ x))).symm
    _ = (y ◇ (z ◇ ((w ◇ u) ◇ (v ◇ x)))):=(congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (apc2 (v ◇ x) (w ◇ u)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_20083_to_7319 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_20083_to_7319
