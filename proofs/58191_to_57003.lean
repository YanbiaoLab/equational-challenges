-- Equation58191 → Equation57003
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ z) = ((w ◇ u) ◇ v) ◇ r
-- Conclusion: x ◇ (y ◇ z) = (x ◇ (w ◇ y)) ◇ u
-- Original submission SHA-256: cfa63a6e4fd06640a136b0792e6169de26d6495fd4a066966c86dcb341ee2047
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G) (r : G), x ◇ (y ◇ z) = ((w ◇ u) ◇ v) ◇ r
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = (x ◇ (w ◇ y)) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have p0 : forall (q0 q1 q2 q3 q4 q5:G), (q3 ◇ (q4 ◇ q5)) = (q0 ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((h q0 q1 q2 q0 q0 q0 q0).trans ((h q3 q4 q5 q0 q0 q0 q0).symm)).symm
  have p1 : forall (q0 q1 q2 q6 q3 q4 q5:G), ((q0 ◇ (q1 ◇ q2)) ◇ q6) = (q3 ◇ (q4 ◇ q5)):=by
    intro q0 q1 q2 q6 q3 q4 q5
    exact ((congrArg (fun t => t ◇ q6) ((h q0 q1 q2 q0 q0 q0 q0).symm)).symm).trans ((h q3 q4 q5 (q0 ◇ q0) q0 q0 q6).symm)
  exact (p0 u w z x y z).trans ((p1 x w y u u w z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_58191_to_57003 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_58191_to_57003
