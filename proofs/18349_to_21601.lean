-- Equation18349 → Equation21601
-- Recorded verdict: true
-- Premise: x = (y * y) * (z * ((w * u) * x))
-- Conclusion: x = (y * (x * y)) * (x * (y * x))
-- Original submission SHA-256: 71b35ad47d792bf805c1995786cd5325f4e79e4fea2268d01d1d331c95345317
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ y) ◇ (z ◇ ((w ◇ u) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ (x ◇ y)) ◇ (x ◇ (y ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3:G), ((q2 ◇ q2) ◇ (q3 ◇ (q0 ◇ q1))) = q1:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => (q2 ◇ q2) ◇ t) (congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ q1) ((h q0 q0 q0 q0 q0).symm)))).symm).trans ((h q1 q2 q3 (q0 ◇ q0) (q0 ◇ ((q0 ◇ q0) ◇ q0))).symm)
  have apc1 : forall (q4 q5 q6 q7:G), (q4 ◇ (q7 ◇ (q5 ◇ q6))) = q6:=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => t ◇ (q7 ◇ (q5 ◇ q6))) (apc0 q4 q4 (q4 ◇ q4) (q4 ◇ q4))).symm).trans (apc0 q5 q6 ((q4 ◇ q4) ◇ (q4 ◇ q4)) q7)
  exact (calc
    x = x:=rfl
    _ = ((y ◇ (x ◇ y)) ◇ (x ◇ (y ◇ x))):=(apc1 (y ◇ (x ◇ y)) y x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_18349_to_21601 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_18349_to_21601
