-- Equation8194 → Equation59866
-- Recorded verdict: true
-- Premise: x = y * (z * ((w * (u * u)) * u))
-- Conclusion: (x * y) * z = w * ((z * y) * u)
-- Original submission SHA-256: ca18f4500e19e39aab78649bc3c445c945c923f754ebc8b11838e58cd48171af
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ (z ◇ ((w ◇ (u ◇ u)) ◇ u))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = w ◇ ((z ◇ y) ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc1 : forall (q0 q1 q2:G), (q2 ◇ q0) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) ((h q0 q0 (q0 ◇ (((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0))) q0 q0).symm)).symm).trans ((h q1 q2 q0 q0 ((q0 ◇ (q0 ◇ q0)) ◇ q0)).symm)
  exact (apc1 z ((x ◇ y) ◇ z) (x ◇ y)).trans ((apc1 ((z ◇ y) ◇ u) ((x ◇ y) ◇ z) w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_8194_to_59866 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_8194_to_59866
