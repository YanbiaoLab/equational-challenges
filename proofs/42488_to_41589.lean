-- Equation42488 → Equation41589
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (x ◇ ((z ◇ z) ◇ z))
-- Conclusion: x ◇ x = y ◇ (x ◇ (x ◇ (z ◇ z)))
-- Original submission SHA-256: 75b810621ee09c20ff7ed1b06b9a3ce386d37157dd699d0b5e6615849bb6f7fa
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (x ◇ ((z ◇ z) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (x ◇ (x ◇ (z ◇ z)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have p0 : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ (q0 ◇ q0))) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => q1 ◇ t) ((h q0 ((q0 ◇ ((q0 ◇ q0) ◇ q0)) ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) q0).symm))).symm).trans ((h q1 q2 (q0 ◇ ((q0 ◇ q0) ◇ q0))).symm)
  have p1 : forall (q0 q1 q2:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact ((p0 q0 (q0 ◇ q0) q2).symm).trans (((congrArg (fun t => q2 ◇ t) (p0 q0 (q0 ◇ q0) q1)).symm).trans (p0 (q0 ◇ q0) q1 q2))
  exact ((p1 x x x).symm).trans ((((congrArg (fun t => y ◇ t) (p0 z x x)).trans (congrArg (fun t => y ◇ t) ((p1 x x x).symm))).trans (p0 x (x ◇ x) y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42488_to_41589 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42488_to_41589
