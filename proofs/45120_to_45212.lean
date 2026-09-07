-- Equation45120 → Equation45212
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (((x ◇ z) ◇ z) ◇ w)
-- Conclusion: x ◇ x = y ◇ (((z ◇ z) ◇ w) ◇ w)
-- Original submission SHA-256: 5eeb4c11888088ba7315d123c181d39f45d035713dcdd377727a1fed12d112f1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (((x ◇ z) ◇ z) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (((z ◇ z) ◇ w) ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have p0 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) ((h q0 ((q1 ◇ q0) ◇ q0) q0 q0).symm)).symm).trans ((h q1 q2 q0 (((q0 ◇ q0) ◇ q0) ◇ q0)).symm)
  have p1 : forall (q0 q1 q2:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact ((p0 q0 q1 q2).symm).trans (p0 q0 q0 q2)
  exact (p1 w x w).trans (((congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ w) (congrArg (fun t => t ◇ w) (p1 w z w)))).trans ((h w y w w).symm)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45120_to_45212 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45120_to_45212
