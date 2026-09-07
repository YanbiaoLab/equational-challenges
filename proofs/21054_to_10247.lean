-- Equation21054 → Equation10247
-- Recorded verdict: true
-- Premise: x = (y ◇ z) ◇ (((x ◇ w) ◇ w) ◇ z)
-- Conclusion: x = y ◇ ((x ◇ z) ◇ ((x ◇ w) ◇ y))
-- Original submission SHA-256: d108efff2ddf6ea2704959dda58b033a70826d8c031be5e0f858a4d9e2183b04
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ (((x ◇ w) ◇ w) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((x ◇ z) ◇ ((x ◇ w) ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q1 ◇ (((q4 ◇ q3) ◇ q3) ◇ (((q1 ◇ q0) ◇ q0) ◇ q2))) = q4:=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ (((q4 ◇ q3) ◇ q3) ◇ (((q1 ◇ q0) ◇ q0) ◇ q2))) ((h q1 q0 q2 q0).symm)).symm).trans ((h q4 (q0 ◇ q2) (((q1 ◇ q0) ◇ q0) ◇ q2) q3).symm)
  have apc1 : forall (q5 q6:G), (q5 ◇ q5) = q6:=by
    intro q5 q6
    exact ((congrArg (fun t => q5 ◇ t) (apc0 q5 ((q6 ◇ q5) ◇ q5) q5 q5 q5)).symm).trans (apc0 q5 q5 (((((q6 ◇ q5) ◇ q5) ◇ q5) ◇ q5) ◇ q5) q5 q6)
  exact ((apc1 x x).symm).trans (apc1 x (y ◇ ((x ◇ z) ◇ ((x ◇ w) ◇ y))))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_21054_to_10247 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_21054_to_10247
