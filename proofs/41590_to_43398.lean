-- Equation41590 → Equation43398
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (x ◇ (x ◇ (z ◇ w)))
-- Conclusion: x ◇ x = y ◇ ((y ◇ z) ◇ (y ◇ z))
-- Original submission SHA-256: 58c8fec96a9244bea9297e44af4e253bb5e4d12747e8b2c11658ebe5f629e6e2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (x ◇ (x ◇ (z ◇ w)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ ((y ◇ z) ◇ (y ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  calc
    (x ◇ x) = (y ◇ ((y ◇ z) ◇ (y ◇ z))):=(((((((((((h x y x (x ◇ x)).trans (congrArg (fun t => y ◇ t) ((h x x x x).symm))).trans (congrArg (fun t => y ◇ t) (h x (y ◇ z) x (x ◇ x)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => (y ◇ z) ◇ t) ((h x x x x).symm)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => (y ◇ z) ◇ t) (h x y x (x ◇ x))))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => (y ◇ z) ◇ t) (congrArg (fun t => y ◇ t) ((h x x x x).symm))))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => (y ◇ z) ◇ t) (congrArg (fun t => y ◇ t) (h x y x x))))).trans (congrArg (fun t => y ◇ t) ((h y (y ◇ z) x (x ◇ (x ◇ x))).symm))).trans (congrArg (fun t => y ◇ t) (h y (y ◇ z) y (x ◇ x)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => (y ◇ z) ◇ t) ((h y y x x).symm)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => (y ◇ z) ◇ t) (h y (y ◇ z) (y ◇ z) (y ◇ z))))).trans ((((congrArg (fun t => y ◇ t) (h (y ◇ z) (y ◇ z) x x)).trans ((h (y ◇ z) y (y ◇ z) (x ◇ x)).symm)).trans (h (y ◇ z) y y (y ◇ ((y ◇ z) ◇ (y ◇ z))))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41590_to_43398 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41590_to_43398
