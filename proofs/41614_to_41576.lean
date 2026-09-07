-- Equation41614 → Equation41576
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (x ◇ (z ◇ (w ◇ y)))
-- Conclusion: x ◇ x = x ◇ (y ◇ (z ◇ (w ◇ x)))
-- Original submission SHA-256: dcc88a79c5d63f32d953f3ce888290d32707d0f678cf5dd906230acc74eb0c66
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (x ◇ (z ◇ (w ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = x ◇ (y ◇ (z ◇ (w ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have p0 : forall (q0 q1 q2:G), ((q0 ◇ q1) ◇ (q2 ◇ q2)) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q0 ◇ q1) ◇ t) ((h q2 q1 q0 q0).symm)).symm).trans ((h q1 (q0 ◇ q1) q2 q0).symm)
  have p1 : forall (q0 q1 q2:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((p0 q0 q0 q2).symm).trans ((((congrArg (fun t => t ◇ (q2 ◇ q2)) (p0 q0 q0 q1)).symm).trans (p0 (q0 ◇ q0) (q1 ◇ q1) q2)).trans (p0 q1 q1 q1))).symm
  exact (calc
    (x ◇ x) = (y ◇ y):=p1 y x w
    _ = (x ◇ (y ◇ (z ◇ (w ◇ x)))):=((h y x z w).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41614_to_41576 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41614_to_41576
