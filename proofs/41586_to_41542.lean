-- Equation41586 → Equation41542
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (x ◇ (x ◇ (y ◇ z)))
-- Conclusion: x ◇ x = x ◇ (x ◇ (y ◇ (z ◇ z)))
-- Original submission SHA-256: 0f4ab6aff4e04c0f52810a188269f1d0e900303e1c5359cc67564d14c4cbcc1b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (x ◇ (x ◇ (y ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = x ◇ (x ◇ (y ◇ (z ◇ z)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  calc
    (x ◇ x) = (x ◇ (x ◇ (y ◇ (z ◇ z)))):=((((((((((h x z (x ◇ x)).trans (congrArg (fun t => z ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => z ◇ t) (h x z x)))))).trans (congrArg (fun t => z ◇ t) (congrArg (fun t => x ◇ t) ((h z x (x ◇ (z ◇ x))).symm)))).trans (congrArg (fun t => z ◇ t) (congrArg (fun t => x ◇ t) (h z z (z ◇ z))))).trans (congrArg (fun t => z ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => z ◇ t) ((h z z z).symm))))).trans (congrArg (fun t => z ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => z ◇ t) (h z z (z ◇ z)))))).trans (congrArg (fun t => z ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => z ◇ t) (congrArg (fun t => z ◇ t) ((h z z z).symm)))))).trans (congrArg (fun t => z ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => z ◇ t) (congrArg (fun t => z ◇ t) (h z x x)))))).trans (congrArg (fun t => z ◇ t) ((h z x (z ◇ (z ◇ (x ◇ x)))).symm))).trans (congrArg (fun t => z ◇ t) (h z z z))).trans ((((((((((((((((((((congrArg (fun t => x ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => y ◇ t) (h z z (z ◇ z))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) ((h z z z).symm)))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (h z z (z ◇ z))))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (congrArg (fun t => z ◇ t) ((h z z z).symm))))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (congrArg (fun t => z ◇ t) (h z y x))))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => x ◇ t) ((h z y (z ◇ (z ◇ (y ◇ x)))).symm)))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => x ◇ t) (h z z (z ◇ z))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => z ◇ t) ((h z z z).symm))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => z ◇ t) (h z z (z ◇ z)))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => z ◇ t) (congrArg (fun t => z ◇ t) ((h z z z).symm)))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => z ◇ t) (congrArg (fun t => z ◇ t) (h z x x)))))).trans (congrArg (fun t => x ◇ t) ((h z x (z ◇ (z ◇ (x ◇ x)))).symm))).trans (congrArg (fun t => x ◇ t) (h z z (z ◇ z)))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => z ◇ t) ((h z z z).symm)))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => z ◇ t) (h z z (z ◇ z))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => z ◇ t) (congrArg (fun t => z ◇ t) ((h z z z).symm))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => z ◇ t) (congrArg (fun t => z ◇ t) (h z x x))))).trans ((h z x (z ◇ (z ◇ (x ◇ x)))).symm)).trans (h z z (z ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41586_to_41542 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41586_to_41542
