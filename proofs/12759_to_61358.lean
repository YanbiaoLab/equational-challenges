-- Equation12759 → Equation61358
-- Recorded verdict: true
-- Premise: x = x * ((y * (z * (z * z))) * w)
-- Conclusion: (x * y) * z = (x * (y * w)) * y
-- Original submission SHA-256: 7775bcee669f745675169b786ef42908c2745ec7706bae2156ec14740324af21
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ ((y ◇ (z ◇ (z ◇ z))) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = (x ◇ (y ◇ w)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ (q2 ◇ q0)) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q1 ◇ t) (congrArg (fun t => t ◇ q0) ((h q2 q0 q0 ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0))))).symm))).symm).trans ((h q1 q2 (q0 ◇ (q0 ◇ (q0 ◇ q0))) q0).symm)
  have apc1 : forall (q3 q4:G), (q3 ◇ q4) = q3:=by
    intro q3 q4
    exact ((congrArg (fun t => q3 ◇ t) (apc0 q3 q4 q3)).symm).trans (apc0 (q3 ◇ q3) q3 q4)
  exact (calc
    ((x ◇ y) ◇ z) = x:=(congrArg (fun t => t ◇ z) (apc1 x y)).trans (apc1 x z)
    _ = ((x ◇ (y ◇ w)) ◇ y):=(((congrArg (fun t => t ◇ y) (congrArg (fun t => x ◇ t) (apc1 y w))).trans (congrArg (fun t => t ◇ y) (apc1 x y))).trans (apc1 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_12759_to_61358 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_12759_to_61358
