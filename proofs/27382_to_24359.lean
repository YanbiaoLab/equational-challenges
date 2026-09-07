-- Equation27382 → Equation24359
-- Recorded verdict: true
-- Premise: x = ((y * z) * (w * y)) * (x * x)
-- Conclusion: x = ((y * y) * x) * ((y * z) * x)
-- Original submission SHA-256: d1cb6271f11e577523521d19bc956a0cb3363c4cfdac37be25524a89ed79a16d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ (w ◇ y)) ◇ (x ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ x) ◇ ((y ◇ z) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q0 ◇ q1) ◇ (q2 ◇ q2)) = q2:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q2 ◇ q2)) ((h (q0 ◇ q1) q0 q1 q0).symm)).symm).trans ((h q2 (q0 ◇ q1) (q0 ◇ q0) (q0 ◇ q1)).symm)
  have apc1 : forall (q3 q4:G), (q4 ◇ (q3 ◇ q3)) = q3:=by
    intro q3 q4
    exact ((congrArg (fun t => t ◇ (q3 ◇ q3)) (apc0 q4 q3 q4)).symm).trans ((h q3 q4 q3 q4).symm)
  have apc3 : forall (q5 q6:G), (q6 ◇ q5) = (q5 ◇ q5):=by
    intro q5 q6
    exact ((congrArg (fun t => q6 ◇ t) (apc1 q5 (q5 ◇ q5))).symm).trans (apc1 (q5 ◇ q5) q6)
  exact (calc
    x = x:=rfl
    _ = (((y ◇ y) ◇ x) ◇ ((y ◇ z) ◇ x)):=(((congrArg (fun t => t ◇ ((y ◇ z) ◇ x)) (apc3 x (y ◇ y))).trans (congrArg (fun t => (x ◇ x) ◇ t) (apc3 x (y ◇ z)))).trans (apc1 x (x ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_27382_to_24359 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_27382_to_24359
