-- Equation42478 → Equation43460
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (x ◇ ((z ◇ x) ◇ x))
-- Conclusion: x ◇ x = y ◇ ((z ◇ w) ◇ (x ◇ x))
-- Original submission SHA-256: 683d92f6428fc4fd77027af5dadab981537ba9c922c2420d6add674fd02d1d9e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (x ◇ ((z ◇ x) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ ((z ◇ w) ◇ (x ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z:G), (y ◇ (x ◇ ((z ◇ x) ◇ x))) = (x ◇ (x ◇ ((x ◇ x) ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (q0:G), (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) = (q0 ◇ q0):=by
    intro q0
    exact ((apc0 q0 q0 q0).symm).trans ((h q0 q0 q0).symm)
  have apc2 : forall (q1 q2 q3:G), ((q1 ◇ ((q2 ◇ q1) ◇ q1)) ◇ (q1 ◇ ((q2 ◇ q1) ◇ q1))) = (q3 ◇ ((q1 ◇ ((q2 ◇ q1) ◇ q1)) ◇ (q1 ◇ q1))):=by
    intro q1 q2 q3
    exact (((congrArg (fun t => q3 ◇ t) (congrArg (fun t => (q1 ◇ ((q2 ◇ q1) ◇ q1)) ◇ t) (apc1 q1))).symm).trans (((congrArg (fun t => q3 ◇ t) (congrArg (fun t => (q1 ◇ ((q2 ◇ q1) ◇ q1)) ◇ t) (apc0 q1 (q1 ◇ (q1 ◇ ((q2 ◇ q1) ◇ q1))) q2))).symm).trans ((h (q1 ◇ ((q2 ◇ q1) ◇ q1)) q3 q1).symm))).symm
  have apc3 : forall (q4 q5 q6:G), (q4 ◇ ((q5 ◇ ((q6 ◇ q5) ◇ q5)) ◇ (q5 ◇ q5))) = (q5 ◇ q5):=by
    intro q4 q5 q6
    exact ((apc2 q5 q6 q4).symm).trans ((h q5 (q5 ◇ ((q6 ◇ q5) ◇ q5)) q6).symm)
  have apc4 : forall (q7 q8 q9:G), (q9 ◇ (((q7 ◇ ((q8 ◇ q7) ◇ q7)) ◇ (q7 ◇ q7)) ◇ (q7 ◇ q7))) = (q7 ◇ q7):=by
    intro q7 q8 q9
    exact (((congrArg (fun t => q9 ◇ t) (congrArg (fun t => ((q7 ◇ ((q8 ◇ q7) ◇ q7)) ◇ (q7 ◇ q7)) ◇ t) (apc3 (q7 ◇ ((q7 ◇ ((q8 ◇ q7) ◇ q7)) ◇ (q7 ◇ q7))) q7 q8))).symm).trans ((h ((q7 ◇ ((q8 ◇ q7) ◇ q7)) ◇ (q7 ◇ q7)) q9 q7).symm)).trans (apc3 ((q7 ◇ ((q8 ◇ q7) ◇ q7)) ◇ (q7 ◇ q7)) q7 q8)
  have apc6 : forall (q10 q11:G), ((q10 ◇ q10) ◇ (q10 ◇ q10)) = (q11 ◇ (q10 ◇ q10)):=by
    intro q10 q11
    exact (((congrArg (fun t => q11 ◇ t) (apc4 q10 q10 (q10 ◇ q10))).symm).trans ((h (q10 ◇ q10) q11 (q10 ◇ ((q10 ◇ q10) ◇ q10))).symm)).symm
  have apc7 : forall (q12 q13:G), (q12 ◇ ((q13 ◇ q13) ◇ (q13 ◇ q13))) = (q13 ◇ q13):=by
    intro q12 q13
    exact ((congrArg (fun t => q12 ◇ t) ((apc6 q13 (q13 ◇ ((q12 ◇ q13) ◇ q13))).symm)).symm).trans (apc3 q12 q13 q12)
  have apc8 : forall (q14 q15 q16:G), (q15 ◇ (q14 ◇ (q16 ◇ q16))) = (q16 ◇ q16):=by
    intro q14 q15 q16
    exact ((congrArg (fun t => q15 ◇ t) (apc6 q16 q14)).symm).trans (apc7 q15 q16)
  have apc9 : forall (q10 q11:G), (q11 ◇ (q10 ◇ q10)) = (q10 ◇ (q10 ◇ q10)):=by
    intro q10 q11
    exact ((apc6 q10 q11).symm).trans (apc6 q10 q10)
  exact (calc
    (x ◇ x) = (x ◇ x):=rfl
    _ = (y ◇ ((z ◇ w) ◇ (x ◇ x))):=((congrArg (fun t => y ◇ t) (apc9 x (z ◇ w))).trans (apc8 x y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42478_to_43460 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42478_to_43460
