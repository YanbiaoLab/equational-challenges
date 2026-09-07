-- Equation13087 → Equation25263
-- Recorded verdict: true
-- Premise: x = y * ((y * (z * (w * u))) * x)
-- Conclusion: x = (y * (y * (y * x))) * (z * x)
-- Original submission SHA-256: 0ffc2bb273a299246773f759d14f7a383a03934f295589dbb0e60865c50618a7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ ((y ◇ (z ◇ (w ◇ u))) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ (y ◇ x))) ◇ (z ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (q3 ◇ ((q1 ◇ q0) ◇ q2)) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ q2) ((h (q1 ◇ q0) q3 q0 q0 q0).symm))).symm).trans ((h q2 q3 (q3 ◇ (q0 ◇ (q0 ◇ q0))) q1 q0).symm)
  have apc1 : forall (q4 q5 q6:G), (q6 ◇ (q4 ◇ q5)) = q5:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => q6 ◇ t) (congrArg (fun t => t ◇ q5) (apc0 q4 q4 q4 q4))).symm).trans (apc0 ((q4 ◇ q4) ◇ q4) q4 q5 q6)
  exact (calc
    x = x:=rfl
    _ = ((y ◇ (y ◇ (y ◇ x))) ◇ (z ◇ x)):=((congrArg (fun t => t ◇ (z ◇ x)) (congrArg (fun t => y ◇ t) (apc1 y x y))).trans (apc1 z x (y ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_13087_to_25263 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_13087_to_25263
