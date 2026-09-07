-- Equation3501 → Equation53830
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ ((z ◇ z) ◇ z)
-- Conclusion: x ◇ (x ◇ x) = y ◇ (x ◇ (z ◇ z))
-- Original submission SHA-256: 37bd1023ff21ab90385577fb005df5528edc00540ad58526d94e324d349c2ec6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ ((z ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ x) = y ◇ (x ◇ (z ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  calc
    (x ◇ (x ◇ x)) = (y ◇ (x ◇ (z ◇ z))):=(((((((((congrArg (fun t => x ◇ t) (h x x z)).trans (congrArg (fun t => x ◇ t) ((h (z ◇ z) x z).symm))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ (z ◇ z)) (h z x x)))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ (z ◇ z)) ((h (z ◇ z) x x).symm)))).trans ((h y x (z ◇ z)).symm)).trans (h y y (z ◇ z))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ (z ◇ z)) (h (z ◇ z) x x)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ (z ◇ z)) ((h z x x).symm)))).trans (congrArg (fun t => y ◇ t) (h (z ◇ z) x ((z ◇ z) ◇ z)))).trans (((congrArg (fun t => y ◇ t) (congrArg (fun t => x ◇ t) (h z (x ◇ x) z))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ ((z ◇ z) ◇ z)) (h x ((z ◇ z) ◇ z) z))))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3501_to_53830 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3501_to_53830
