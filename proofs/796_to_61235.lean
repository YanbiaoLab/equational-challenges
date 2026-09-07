-- Equation796 → Equation61235
-- Recorded verdict: true
-- Premise: x = y * (z * ((w * y) * x))
-- Conclusion: (x * y) * y = (y * (z * x)) * y
-- Original submission SHA-256: d415ae623a8bd65ac3e472b42b485213064b2cfaaa966997faca629d31ea06d4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (z ◇ ((w ◇ y) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ y = (y ◇ (z ◇ x)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), ((q0 ◇ q3) ◇ q1) = (q2 ◇ q1):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => q2 ◇ t) ((h q1 q3 (q0 ◇ q2) q0).symm)).symm).trans ((h ((q0 ◇ q3) ◇ q1) q2 q3 q0).symm)).symm
  exact (apc0 x y ((x ◇ y) ◇ y) y).trans ((apc0 y y ((x ◇ y) ◇ y) (z ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_796_to_61235 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_796_to_61235
