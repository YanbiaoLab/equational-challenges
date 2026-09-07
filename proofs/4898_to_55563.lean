-- Equation4898 → Equation55563
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ (x ◇ (x ◇ (x ◇ x))))
-- Conclusion: x ◇ (x ◇ x) = (x ◇ x) ◇ (y ◇ x)
-- Original submission SHA-256: a426726db87a89862dcf13083fd9075bcaf945b83424ce473353c8378dacf67f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (x ◇ (x ◇ (x ◇ (x ◇ x))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ x) = (x ◇ x) ◇ (y ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f : G → G) {a b : G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc2 : forall (q0 q1 : G), (q1 ◇ ((q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) ◇ ((q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) ◇ ((q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) ◇ q0))))=(q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))):=by
    intro q0 q1
    exact ((rfl).symm).trans ((((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) ◇ t) ((h q0 (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0))))).symm))))).symm).trans ((h (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) q1).symm)).trans (rfl))
  have apc3 : forall (q2 q3 : G), (q3 ◇ (((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ q2))) ◇ (((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ q2))) ◇ (((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ q2))) ◇ (q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2))))))))=((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ q2))):=by
    intro q2 q3
    exact ((rfl).symm).trans ((((cg (fun t => q3 ◇ t) (cg (fun t => ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ q2))) ◇ t) (cg (fun t => ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ q2))) ◇ t) (cg (fun t => ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ q2))) ◇ t) (apc2 q2 ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ q2)))))))).symm).trans ((h ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q2 ◇ (q2 ◇ (q2 ◇ q2)))) ◇ q2))) q3).symm)).trans (rfl))
  have apc4 : forall (q4 q5 : G), (q5 ◇ (((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ ((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ ((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ q4))) ◇ (((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ ((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ ((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ q4))) ◇ q4)))=((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ ((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ ((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ q4))):=by
    intro q4 q5
    exact ((rfl).symm).trans ((((cg (fun t => q5 ◇ t) (cg (fun t => ((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ ((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ ((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ q4))) ◇ t) (cg (fun t => ((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ ((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ ((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ q4))) ◇ t) ((h q4 ((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ ((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ ((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ q4)))).symm)))).symm).trans (apc3 q4 q5)).trans (rfl))
  have apc9 : forall (q6 q7 : G), (q7 ◇ ((((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ q6)) ◇ ((((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ q6)) ◇ (q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))))))=(((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ q6)):=by
    intro q6 q7
    exact ((cg (fun t => q7 ◇ t) (cg (fun t => (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ q6)) ◇ t) (cg (fun t => (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ q6)) ◇ t) (apc2 q6 (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ q6)))))).symm).trans ((((cg (fun t => q7 ◇ t) (cg (fun t => (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ q6)) ◇ t) (cg (fun t => (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ q6)) ◇ t) (cg (fun t => (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ q6)) ◇ t) (apc4 q6 (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ q6))))))).symm).trans ((h (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) ◇ q6)) q7).symm)).trans (rfl))
  have apc10 : forall (q8 q9 : G), (q9 ◇ ((((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ q8))) ◇ (((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ q8))) ◇ q8)) ◇ q8))=(((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ q8))) ◇ (((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ q8))) ◇ q8)):=by
    intro q8 q9
    exact ((rfl).symm).trans ((((cg (fun t => q9 ◇ t) (cg (fun t => (((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ q8))) ◇ (((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ q8))) ◇ q8)) ◇ t) ((h q8 (((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ q8))) ◇ (((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) ◇ q8))) ◇ q8))).symm))).symm).trans (apc9 q8 q9)).trans (rfl))
  have apc11 : forall (q10 q11 : G), (q11 ◇ (((((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ (((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ q10)) ◇ q10) ◇ (q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10))))))=((((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ (((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ q10)) ◇ q10):=by
    intro q10 q11
    exact (((cg (fun t => q11 ◇ t) (cg (fun t => ((((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ (((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ q10)) ◇ q10) ◇ t) (cg (fun t => ((((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ (((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ q10)) ◇ q10) ◇ t) (apc4 q10 ((((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ (((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ q10)) ◇ q10))))).trans (cg (fun t => q11 ◇ t) (cg (fun t => ((((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ (((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ q10)) ◇ q10) ◇ t) (apc2 q10 ((((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ (((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ q10)) ◇ q10))))).symm).trans ((((cg (fun t => q11 ◇ t) (cg (fun t => ((((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ (((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ q10)) ◇ q10) ◇ t) (cg (fun t => ((((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ (((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ q10)) ◇ q10) ◇ t) (cg (fun t => ((((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ (((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ q10)) ◇ q10) ◇ t) (apc10 q10 ((((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ (((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ q10)) ◇ q10)))))).symm).trans ((h ((((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ (((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q10 ◇ (q10 ◇ (q10 ◇ q10)))) ◇ q10))) ◇ q10)) ◇ q10) q11).symm)).trans (rfl))
  have apc17 : forall (q12 q13 : G), ((((q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))) ◇ ((q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))) ◇ ((q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))) ◇ q12))) ◇ (((q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))) ◇ ((q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))) ◇ ((q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))) ◇ q12))) ◇ q12)) ◇ q12)=(q13 ◇ q12):=by
    intro q12 q13
    exact (((rfl).symm).trans ((((cg (fun t => q13 ◇ t) ((h q12 ((((q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))) ◇ ((q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))) ◇ ((q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))) ◇ q12))) ◇ (((q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))) ◇ ((q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))) ◇ ((q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))) ◇ q12))) ◇ q12)) ◇ q12)).symm)).symm).trans (apc11 q12 q13)).trans (rfl))).symm
  have sameRight : ∀ (r a b : G), a ◇ r = b ◇ r := by
    intro r a b
    exact ((apc17 r a).symm).trans (apc17 r b)
  exact (sameRight (x ◇ x) x (x ◇ x)).trans (congrArg (fun t => (x ◇ x) ◇ t) (sameRight x x y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4898_to_55563 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4898_to_55563
