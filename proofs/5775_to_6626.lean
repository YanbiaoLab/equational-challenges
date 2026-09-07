-- Equation5775 → Equation6626
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))
-- Conclusion: x = x ◇ (y ◇ ((z ◇ w) ◇ (x ◇ x)))
-- Original submission SHA-256: 7b2c47a2872c6c4915992ec8a943b72b8bba649d827fbbe4e07528821a3a46ed
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (y ◇ ((z ◇ w) ◇ (x ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (q0 q1:G), (q1 ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0))) = (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ t) ((h q0 ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))))).symm)))).symm).trans ((h (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) q1).symm)
  have p1 : forall (q0 q1:G), (q1 ◇ (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0)))))) = ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ t) (cg (fun t => ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ t) (p0 q0 (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0))))))).symm).trans ((h ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) q1).symm)
  have p2 : forall (q0 q1:G), (q1 ◇ (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0)) = ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ t) ((h q0 ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0))).symm))).symm).trans (p1 q0 q1)
  have p3 : forall (q0 q1:G), (q1 ◇ ((((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0) ◇ (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))))) = (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0) ◇ t) (p0 q0 (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0)))).symm).trans (((cg (fun t => q1 ◇ t) (cg (fun t => (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0) ◇ t) (cg (fun t => (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0) ◇ t) (p2 q0 ((((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0) ◇ (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0)))))).symm).trans ((h (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0) q1).symm))
  have p4 : forall (q0 q1:G), (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0) = (q1 ◇ q0):=by
    intro q0 q1
    exact (((cg (fun t => q1 ◇ t) ((h q0 (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0)).symm)).symm).trans (p3 q0 q1)).symm
  have p5 : forall (q0 q1:G), (q1 ◇ q0) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((p4 q0 q1).symm).trans (p4 q0 q0)
  have p6 : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q1 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact (((((((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q0) (cg (fun t => (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ t) (cg (fun t => t ◇ q0) (cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (p5 q0 (q0 ◇ q0)))))))).trans (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q0) (cg (fun t => t ◇ ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ q0)) (cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (p5 q0 (q0 ◇ q0)))))))).trans (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q0) (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (p5 q0 (q0 ◇ (q0 ◇ (q0 ◇ q0)))))))).trans (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q0) (p5 (q0 ◇ q0) (q0 ◇ (q0 ◇ (q0 ◇ q0))))))).trans (cg (fun t => q1 ◇ t) (p5 q0 ((q0 ◇ q0) ◇ (q0 ◇ q0))))).symm).trans ((p2 q0 q1).trans ((((cg (fun t => (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ t) (cg (fun t => t ◇ q0) (cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (p5 q0 (q0 ◇ q0)))))).trans (cg (fun t => t ◇ ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ q0)) (cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (p5 q0 (q0 ◇ q0)))))).trans (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (p5 q0 (q0 ◇ (q0 ◇ (q0 ◇ q0)))))).trans (p5 (q0 ◇ q0) (q0 ◇ (q0 ◇ (q0 ◇ q0))))))).symm
  have p7 : forall (q0 q1:G), (q1 ◇ (q0 ◇ q0)) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((p6 q0 q1).symm).trans (p6 q0 q0)
  have p8 : forall (x y q0 q1:G), (y ◇ (x ◇ (x ◇ (x ◇ x)))) = x:=by
    intro x y q0 q1
    exact ((h x y).trans (cg (fun t => y ◇ t) (cg (fun t => x ◇ t) (cg (fun t => x ◇ t) (p5 x (x ◇ x)))))).symm
  have p9 : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q0 ◇ q0))) = (q0 ◇ (q0 ◇ (q0 ◇ q0))):=by
    intro q0 q1
    exact ((((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (p5 q0 (q0 ◇ (q0 ◇ (q0 ◇ q0)))))).trans (cg (fun t => q1 ◇ t) (p5 (q0 ◇ q0) (q0 ◇ (q0 ◇ (q0 ◇ q0)))))).trans (cg (fun t => q1 ◇ t) (p7 q0 (q0 ◇ q0)))).symm).trans (((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (p8 q0 ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) q0 q0)))).symm).trans ((h (q0 ◇ (q0 ◇ (q0 ◇ q0))) q1).symm))
  exact (calc
    x = x:=rfl
    _ = (x ◇ (y ◇ ((z ◇ w) ◇ (x ◇ x)))):=((((cg (fun t => x ◇ t) (cg (fun t => y ◇ t) (cg (fun t => t ◇ (x ◇ x)) (p5 w z)))).trans (cg (fun t => x ◇ t) (cg (fun t => y ◇ t) (p7 x (w ◇ w))))).trans (cg (fun t => x ◇ t) (p9 x y))).trans (p8 x x (x ◇ (x ◇ (x ◇ (x ◇ x)))) (x ◇ (x ◇ (x ◇ (x ◇ x)))))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5775_to_6626 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5775_to_6626
