-- Equation3904 → Equation52940
-- Recorded verdict: true
-- Premise: x ◇ x = (y ◇ (z ◇ y)) ◇ w
-- Conclusion: x ◇ x = (((x ◇ x) ◇ y) ◇ y) ◇ z
-- Original submission SHA-256: 82486d992cc755d245690201d3030a2bb85dfb09975a90501ef7c9da91bd8671
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = (y ◇ (z ◇ y)) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (((x ◇ x) ◇ y) ◇ y) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have p0 : forall (q0 q1 q2:G), ((q0 ◇ q0) ◇ q1) = (q2 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) ((h q0 q0 q0 (q0 ◇ (q0 ◇ (q0 ◇ q0)))).symm)).symm).trans ((h q2 (q0 ◇ (q0 ◇ q0)) q0 q1).symm)
  exact (((p0 y z x).symm).trans (congrArg (fun t => t ◇ z) ((p0 y y y).symm))).trans ((congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ y) (p0 x y y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3904_to_52940 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3904_to_52940
