-- Equation23771 → Equation8350
-- Recorded verdict: true
-- Premise: x = ((y * z) * z) * (x * (x * x))
-- Conclusion: x = x * (y * (((z * y) * y) * x))
-- Original submission SHA-256: a3a856e09488d99623f9d5a2823d0357274aaba3a7ea631598e9e3640523bb05
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ z) ◇ (x ◇ (x ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (((z ◇ y) ◇ y) ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), (q0 ◇ (q1 ◇ (q1 ◇ q1))) = q1:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ (q1 ◇ (q1 ◇ q1))) ((h q0 q0 (q0 ◇ (q0 ◇ q0))).symm)).symm).trans ((h q1 (q0 ◇ (q0 ◇ (q0 ◇ q0))) (q0 ◇ (q0 ◇ q0))).symm)
  have apc1 : forall (q2 q3:G), (q3 ◇ ((q2 ◇ (q2 ◇ q2)) ◇ q2)) = (q2 ◇ (q2 ◇ q2)):=by
    intro q2 q3
    exact ((congrArg (fun t => q3 ◇ t) (congrArg (fun t => (q2 ◇ (q2 ◇ q2)) ◇ t) (apc0 (q2 ◇ (q2 ◇ q2)) q2))).symm).trans (apc0 q3 (q2 ◇ (q2 ◇ q2)))
  have apc2 : forall (q4 q5:G), ((q4 ◇ (q4 ◇ q4)) ◇ q4) = (q5 ◇ q4):=by
    intro q4 q5
    exact (((congrArg (fun t => q5 ◇ t) (apc0 ((q4 ◇ (q4 ◇ q4)) ◇ q4) q4)).symm).trans (((congrArg (fun t => q5 ◇ t) (congrArg (fun t => ((q4 ◇ (q4 ◇ q4)) ◇ q4) ◇ t) (apc1 q4 ((q4 ◇ (q4 ◇ q4)) ◇ q4)))).symm).trans (apc0 q5 ((q4 ◇ (q4 ◇ q4)) ◇ q4)))).symm
  have apc3 : forall (q4 q5:G), (q5 ◇ q4) = (q4 ◇ q4):=by
    intro q4 q5
    exact ((apc2 q4 q5).symm).trans (apc2 q4 q4)
  have apc5 : forall (q6 q7 q8:G), (q8 ◇ (q6 ◇ q7)) = (q7 ◇ (q7 ◇ q7)):=by
    intro q6 q7 q8
    exact ((congrArg (fun t => q8 ◇ t) (apc2 q7 q6)).symm).trans (apc1 q7 q8)
  exact (calc
    x = x:=rfl
    _ = (x ◇ (y ◇ (((z ◇ y) ◇ y) ◇ x))):=(((((congrArg (fun t => x ◇ t) (congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ y) (apc3 y z))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ x) (apc3 y (y ◇ y)))))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => y ◇ t) (apc3 x (y ◇ y))))).trans (congrArg (fun t => x ◇ t) (apc5 x x y))).trans (apc0 x x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23771_to_8350 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_23771_to_8350
