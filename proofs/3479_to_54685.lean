-- Equation3479 → Equation54685
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ ((x ◇ z) ◇ z)
-- Conclusion: x ◇ (x ◇ x) = x ◇ ((x ◇ x) ◇ y)
-- Original submission SHA-256: 677ef3f5e67e535bfe94bc53c48b3ceb9ddd6c3b1641ae4319a3dd103960e36e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ ((x ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ x) = x ◇ ((x ◇ x) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  calc
    (x ◇ (x ◇ x)) = (x ◇ ((x ◇ x) ◇ y)):=((((congrArg (fun t => x ◇ t) (h x (x ◇ x) x)).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ ((x ◇ x) ◇ x)) (h x y x)))).trans ((h y x ((x ◇ x) ◇ x)).symm)).trans (h y x y)).trans (((((((((((congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ y) (h x x (x ◇ x)))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ y) (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ (x ◇ x)) (congrArg (fun t => x ◇ t) (h x (x ◇ x) x))))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ y) (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ (x ◇ x)) (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ ((x ◇ x) ◇ x)) (h x x x)))))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ y) (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ (x ◇ x)) ((h x x ((x ◇ x) ◇ x)).symm)))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ y) (congrArg (fun t => x ◇ t) (congrArg (fun t => (x ◇ x) ◇ t) (h x (x ◇ x) x)))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ y) (congrArg (fun t => x ◇ t) (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => t ◇ ((x ◇ x) ◇ x)) (h x x x))))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ y) (congrArg (fun t => x ◇ t) ((h x (x ◇ x) ((x ◇ x) ◇ x)).symm))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ y) (congrArg (fun t => x ◇ t) (h x (x ◇ x) x))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ y) (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ ((x ◇ x) ◇ x)) (h x y x)))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ y) ((h y x ((x ◇ x) ◇ x)).symm)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3479_to_54685 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3479_to_54685
