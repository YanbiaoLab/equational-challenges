-- Equation50279 → Equation61211
-- Recorded verdict: true
-- Premise: x * y = (z * (w * (u * z))) * v
-- Conclusion: (x * y) * y = (x * (z * w)) * z
-- Original submission SHA-256: 4c3d361f7fc187183301b92562f2e427f7c1daeaaa422de3513281dfcc8a0e13
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = (z ◇ (w ◇ (u ◇ z))) ◇ v
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ y = (x ◇ (z ◇ w)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc1 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q1) ◇ q2) = (q3 ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ q2) ((h q0 q1 q0 q0 q0 (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))))).symm)).symm).trans ((h q3 q4 (q0 ◇ (q0 ◇ (q0 ◇ q0))) q0 q0 q2).symm)
  exact (apc1 x y y ((x ◇ y) ◇ y) ((x ◇ (z ◇ w)) ◇ z)).trans ((apc1 x (z ◇ w) z ((x ◇ y) ◇ y) ((x ◇ (z ◇ w)) ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50279_to_61211 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_50279_to_61211
