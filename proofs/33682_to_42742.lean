-- Equation33682 → Equation42742
-- Recorded verdict: true
-- Premise: x = ((x * x) * (y * (z * z))) * w
-- Conclusion: x * y = x * (z * ((w * y) * w))
-- Original submission SHA-256: 2e3e635b5d9ce6cda85332d05354a25e4c6cacb7683e51f0baf9beed41cf7adb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((x ◇ x) ◇ (y ◇ (z ◇ z))) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = x ◇ (z ◇ ((w ◇ y) ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1
    exact (((congrArg (fun t => t ◇ q1) ((h (q0 ◇ q0) (q0 ◇ q0) q0 (q0 ◇ (q0 ◇ q0))).symm)).symm).trans ((h ((q0 ◇ q0) ◇ (q0 ◇ q0)) q0 q0 q1).symm)).symm
  have apc1 : forall (q0 q1:G), ((q0 ◇ q0) ◇ q1) = ((q0 ◇ q0) ◇ q0):=by
    intro q0 q1
    exact ((apc0 q0 q1).symm).trans (apc0 q0 q0)
  have apc2 : forall (q2 q1 q3:G), (((q3 ◇ q3) ◇ q2) ◇ q1) = q3:=by
    intro q2 q1 q3
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => (q3 ◇ q3) ◇ t) ((h q2 q2 q2 (q2 ◇ q2)).symm))).symm).trans ((h q3 ((q2 ◇ q2) ◇ (q2 ◇ (q2 ◇ q2))) q2 q1).symm)
  have apc3 : forall (q4 q5 q6:G), (q4 ◇ q5) = (q4 ◇ q4):=by
    intro q4 q5 q6
    exact ((congrArg (fun t => t ◇ q5) (apc2 q4 q6 q4)).symm).trans (((congrArg (fun t => t ◇ q5) (congrArg (fun t => t ◇ q6) (apc1 q4 (q4 ◇ q4)))).symm).trans (apc2 q6 q5 (q4 ◇ q4)))
  exact (apc3 x y (x ◇ y)).trans ((apc3 x (z ◇ ((w ◇ y) ◇ w)) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_33682_to_42742 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_33682_to_42742
