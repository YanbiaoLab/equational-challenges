-- Equation29736 → Equation32641
-- Recorded verdict: true
-- Premise: x = (y * (y * (z * (w * y)))) * y
-- Conclusion: x = (y * ((z * (w * x)) * u)) * w
-- Original submission SHA-256: 69f78ecadabc685de216acc2b676399e4d89afd4a5dc2430f4c5f8901a48b81f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (y ◇ (z ◇ (w ◇ y)))) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ ((z ◇ (w ◇ x)) ◇ u)) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ (q2 ◇ q0)) ◇ q2) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q2) (congrArg (fun t => q2 ◇ t) (congrArg (fun t => q2 ◇ t) ((h q0 (q0 ◇ q2) q0 q0).symm)))).symm).trans ((h q1 q2 ((q0 ◇ q2) ◇ ((q0 ◇ q2) ◇ (q0 ◇ (q0 ◇ (q0 ◇ q2))))) q0).symm)
  exact ((apc0 ((y ◇ ((z ◇ (w ◇ x)) ◇ u)) ◇ w) x x).symm).trans (apc0 ((y ◇ ((z ◇ (w ◇ x)) ◇ u)) ◇ w) ((y ◇ ((z ◇ (w ◇ x)) ◇ u)) ◇ w) x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_29736_to_32641 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_29736_to_32641
