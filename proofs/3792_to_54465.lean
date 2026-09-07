-- Equation3792 → Equation54465
-- Recorded verdict: true
-- Premise: x * y = (z * x) * (y * w)
-- Conclusion: x * (y * z) = y * (w * (u * v))
-- Original submission SHA-256: cabfec722e691ce0e103c1f34c4749d11099e17002965656fb2c590556f58b98
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ x) ◇ (y ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ (y ◇ z) = y ◇ (w ◇ (u ◇ v))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q4 ◇ q3) ◇ (q0 ◇ q1)) = (q3 ◇ (q2 ◇ q0)):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => (q4 ◇ q3) ◇ t) ((h q0 q1 q2 q0).symm)).symm).trans ((h q3 (q2 ◇ q0) q4 (q1 ◇ q0)).symm)
  have apc2 : forall (q5 q6 q7:G), (q6 ◇ (q5 ◇ q7)) = (q6 ◇ q7):=by
    intro q5 q6 q7
    exact ((apc0 q7 q5 q5 q6 q5).symm).trans ((h q6 q7 q5 q5).symm)
  have apc3 : forall (x y z w:G), ((z ◇ x) ◇ w) = ((x ◇ x) ◇ x):=by
    intro x y z w
    exact ((apc2 y (z ◇ x) w).symm).trans ((((h x y z w).symm).trans (h x y x x)).trans (apc2 y (x ◇ x) x))
  have apc9 : forall (q8 q9 q10 q11:G), ((q8 ◇ q8) ◇ q8) = (q9 ◇ q10):=by
    intro q8 q9 q10 q11
    exact (((apc2 q10 ((q8 ◇ q8) ◇ q8) q11).trans (apc3 q8 (((q8 ◇ q8) ◇ q8) ◇ q11) (q8 ◇ q8) q11)).symm).trans (((congrArg (fun t => t ◇ (q10 ◇ q11)) (apc3 q8 q8 q8 q9)).symm).trans ((h q9 q10 (q8 ◇ q8) q11).symm))
  exact ((apc9 (x ◇ (y ◇ z)) x (y ◇ z) (x ◇ (y ◇ z))).symm).trans (apc9 (x ◇ (y ◇ z)) y (w ◇ (u ◇ v)) (x ◇ (y ◇ z)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3792_to_54465 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3792_to_54465
