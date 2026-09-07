-- Equation18890 → Equation18805
-- Recorded verdict: true
-- Premise: x = (x * y) * ((z * z) * (x * w))
-- Conclusion: x = (x * y) * ((x * z) * (y * z))
-- Original submission SHA-256: 8a2bd3f4ea28d6bca74f5c979a3ea0465e1ad823889e81e3bfe6850cc44cba7f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ y) ◇ ((z ◇ z) ◇ (x ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ ((x ◇ z) ◇ (y ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (((q0 ◇ q1) ◇ q2) ◇ ((q3 ◇ q3) ◇ q0)) = (q0 ◇ q1):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => ((q0 ◇ q1) ◇ q2) ◇ t) (congrArg (fun t => (q3 ◇ q3) ◇ t) ((h q0 q1 q0 q0).symm))).symm).trans ((h (q0 ◇ q1) q2 q3 ((q0 ◇ q0) ◇ (q0 ◇ q0))).symm)
  have apc1 : forall (q4 q5 q6 q7:G), ((q4 ◇ q5) ◇ ((q7 ◇ q7) ◇ (q4 ◇ q5))) = ((q4 ◇ q5) ◇ q6):=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => t ◇ ((q7 ◇ q7) ◇ (q4 ◇ q5))) (apc0 q4 q5 q6 q4)).symm).trans (apc0 (q4 ◇ q5) q6 ((q4 ◇ q4) ◇ q4) q7)
  have apc3 : forall (q8 q9 q10:G), ((q10 ◇ q9) ◇ q8) = q10:=by
    intro q8 q9 q10
    exact ((apc1 q10 q9 q8 q8).symm).trans ((h q10 q9 q8 q9).symm)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ y) ◇ ((x ◇ z) ◇ (y ◇ z))):=((congrArg (fun t => (x ◇ y) ◇ t) (apc3 (y ◇ z) z x)).trans (apc3 x y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_18890_to_18805 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_18890_to_18805
