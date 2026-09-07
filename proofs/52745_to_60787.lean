-- Equation52745 → Equation60787
-- Recorded verdict: true
-- Premise: x * y = ((z * (z * y)) * w) * u
-- Conclusion: (x * y) * z = (w * u) * (x * y)
-- Original submission SHA-256: dd2ebba6b3eaaa427ec303e3faab34bae6025012a39f9ba825643213d5fdd6a1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ (z ◇ y)) ◇ w) ◇ u
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = (w ◇ u) ◇ (x ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q1) ◇ q2) = (q3 ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ q2) ((h q0 q1 q0 ((q0 ◇ (q0 ◇ q1)) ◇ q4) q0).symm)).symm).trans ((h q3 q4 (q0 ◇ (q0 ◇ q1)) q0 q2).symm)
  exact (apc0 x y z ((x ◇ y) ◇ z) ((w ◇ u) ◇ (x ◇ y))).trans ((apc0 w u (x ◇ y) ((x ◇ y) ◇ z) ((w ◇ u) ◇ (x ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52745_to_60787 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52745_to_60787
