-- Equation2596 → Equation58053
-- Recorded verdict: true
-- Premise: x = (y * ((z * y) * w)) * x
-- Conclusion: x * (y * z) = ((w * x) * x) * z
-- Original submission SHA-256: 8157dc0a86e6ce329776cfb927c5b49793ae758d617e884ae411a07afba28a5d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ ((z ◇ y) ◇ w)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = ((w ◇ x) ◇ x) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((((q1 ◇ q4) ◇ q0) ◇ q2) ◇ q3) = q3:=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ q3) (congrArg (fun t => ((q1 ◇ q4) ◇ q0) ◇ t) ((h q2 q4 q1 q0).symm))).symm).trans ((h q3 ((q1 ◇ q4) ◇ q0) q4 q2).symm)
  have apc3 : forall (q5 q6:G), (q5 ◇ q6) = q6:=by
    intro q5 q6
    exact ((congrArg (fun t => t ◇ q6) (apc0 q5 q5 q5 q5 q5)).symm).trans (apc0 q5 (q5 ◇ q5) q5 q6 q5)
  exact (calc
    (x ◇ (y ◇ z)) = z:=(congrArg (fun t => x ◇ t) (apc3 y z)).trans (apc3 x z)
    _ = (((w ◇ x) ◇ x) ◇ z):=(((congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ x) (apc3 w x))).trans (congrArg (fun t => t ◇ z) (apc3 x x))).trans (apc3 x z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_2596_to_58053 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_2596_to_58053
