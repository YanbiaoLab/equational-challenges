-- Equation6678 → Equation6697
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ ((x ◇ z) ◇ (y ◇ z)))
-- Conclusion: x = y ◇ (x ◇ ((y ◇ x) ◇ (z ◇ z)))
-- Original submission SHA-256: f788ad699a548e612eb65dc47e019c318028ae8baad896894e9e03adcd1a3ad7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((x ◇ z) ◇ (y ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((y ◇ x) ◇ (z ◇ z)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (q0 q1:G), (((q1 ◇ (q1 ◇ q0)) ◇ q0) ◇ (q1 ◇ (q1 ◇ q0))) = q1:=by
    intro q0 q1
    exact ((cg (fun t => ((q1 ◇ (q1 ◇ q0)) ◇ q0) ◇ t) ((h (q1 ◇ (q1 ◇ q0)) q1 q0).symm)).symm).trans ((h q1 ((q1 ◇ (q1 ◇ q0)) ◇ q0) (q1 ◇ q0)).symm)
  have p1 : forall (x y z:G), (y ◇ (x ◇ ((x ◇ z) ◇ (y ◇ z)))) = (x ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have p2 : forall (x y z:G), (x ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))) = x:=by
    intro x y z
    exact ((h x x x).trans (p1 x x x)).symm
  have p3 : forall (q0:G), ((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0) = q0:=by
    intro q0
    exact ((cg (fun t => (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (p2 q0 (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))))).symm).trans (((cg (fun t => t ◇ (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (p2 q0 q0 q0))).symm).trans (p0 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q0))
  have p4 : forall (q0:G), (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = ((q0 ◇ q0) ◇ q0):=by
    intro q0
    exact (((((cg (fun t => t ◇ ((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ ((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0))) (cg (fun t => t ◇ q0) (p3 q0))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (p3 q0)))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (p3 q0))).symm).trans (((cg (fun t => t ◇ ((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ ((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0))) (cg (fun t => t ◇ q0) (cg (fun t => (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (p3 q0)))).symm).trans (p0 q0 (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))))).symm
  have p5 : forall (x y z q0:G), (x ◇ ((x ◇ x) ◇ x)) = x:=by
    intro x y z q0
    exact ((cg (fun t => x ◇ t) (p4 x)).symm).trans (p2 x x x)
  have p6 : forall (q0:G), (((q0 ◇ q0) ◇ q0) ◇ q0) = q0:=by
    intro q0
    exact ((cg (fun t => t ◇ q0) (p4 q0)).symm).trans (p3 q0)
  have p7 : forall (q0:G), (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ (q0 ◇ q0)) = q0:=by
    intro q0
    exact ((cg (fun t => ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ t) (cg (fun t => q0 ◇ t) (p5 q0 (q0 ◇ ((q0 ◇ q0) ◇ q0)) (q0 ◇ ((q0 ◇ q0) ◇ q0)) (q0 ◇ ((q0 ◇ q0) ◇ q0))))).symm).trans (((cg (fun t => t ◇ (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0)))) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (cg (fun t => q0 ◇ t) (p5 q0 q0 q0 q0)))).symm).trans (p0 ((q0 ◇ q0) ◇ q0) q0))
  have p8 : forall (q0 q1:G), (((q1 ◇ q1) ◇ q1) ◇ (q0 ◇ ((q0 ◇ q1) ◇ q1))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => ((q1 ◇ q1) ◇ q1) ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (p6 q1)))).symm).trans ((h q0 ((q1 ◇ q1) ◇ q1) q1).symm)
  have p9 : forall (q0:G), (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p6 q0))).symm).trans (p8 (q0 ◇ q0) q0)
  have pa : forall (q0:G), ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p9 q0))).symm).trans ((h (q0 ◇ q0) (q0 ◇ q0) q0).symm)
  have pb : forall (q0:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact (((cg (fun t => ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (pa q0))).trans (p6 ((q0 ◇ q0) ◇ (q0 ◇ q0)))).symm).trans (((cg (fun t => ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (pa q0)))).symm).trans (p8 (q0 ◇ q0) ((q0 ◇ q0) ◇ (q0 ◇ q0))))
  have pc : forall (q0 q1 q2 q3:G), (q3 ◇ (q2 ◇ (q0 ◇ (q3 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1))))))) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q3 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1))))) ((h q0 q2 q1).symm)))).symm).trans ((h q2 q3 (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))).symm)
  have pd : forall (q0 q1:G), (q1 ◇ (q1 ◇ (q0 ◇ q0))) = q1:=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) ((h q0 q1 q0).symm)))).symm).trans (pc q0 q0 q1 q1)
  have pe : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q0)) ◇ q1) = q1:=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ (q0 ◇ q0)) ◇ t) (pd q0 q1)).symm).trans (((cg (fun t => (q1 ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (pd q0 (q1 ◇ (q0 ◇ q0))))).symm).trans ((h q1 (q1 ◇ (q0 ◇ q0)) (q0 ◇ q0)).symm))
  have pf : forall (q0 q1:G), (q1 ◇ (q0 ◇ q0)) = ((q1 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact (((((cg (fun t => t ◇ ((q1 ◇ (q0 ◇ q0)) ◇ ((q1 ◇ (q0 ◇ q0)) ◇ q1))) (cg (fun t => t ◇ q1) (pe q0 q1))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q0)) ◇ t) (pe q0 q1)))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (pe q0 q1))).symm).trans (((cg (fun t => t ◇ ((q1 ◇ (q0 ◇ q0)) ◇ ((q1 ◇ (q0 ◇ q0)) ◇ q1))) (cg (fun t => t ◇ q1) (cg (fun t => (q1 ◇ (q0 ◇ q0)) ◇ t) (pe q0 q1)))).symm).trans (p0 q1 (q1 ◇ (q0 ◇ q0))))).symm
  have pg : forall (q0 q1:G), (((q1 ◇ q1) ◇ (q0 ◇ q0)) ◇ (q1 ◇ q1)) = ((q1 ◇ q1) ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => ((q1 ◇ q1) ◇ (q0 ◇ q0)) ◇ t) (pe q0 (q1 ◇ q1))).symm).trans (pd q1 ((q1 ◇ q1) ◇ (q0 ◇ q0)))
  have ph : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q0 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((((cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => t ◇ (q1 ◇ q1)) (pb q1))).trans (cg (fun t => t ◇ (q1 ◇ q1)) (pb q1))).trans (pb q1)).symm).trans (((cg (fun t => t ◇ (q1 ◇ q1)) (pf q0 (q1 ◇ q1))).symm).trans (pg q0 q1))).symm
  have pi : forall (q0 q1:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1
    exact (((((((cg (fun t => t ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ (q0 ◇ q0)))) (cg (fun t => t ◇ (q0 ◇ q0)) (ph q0 q0))).trans (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (ph q0 q1)))).trans (cg (fun t => t ◇ ((q1 ◇ q1) ◇ (q1 ◇ q1))) (ph q0 q0))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (ph q1 q1))).trans (ph q1 q0)).symm).trans (((cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ (q0 ◇ q0)) (ph q0 q1)))).symm).trans (p8 (q1 ◇ q1) (q0 ◇ q0)))).symm
  have pj : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q0) ◇ q1)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (pi q0 q1))).symm).trans (p5 q1 q0 q0 q0)
  have pk : forall (q0 q1:G), (((q0 ◇ q0) ◇ q1) ◇ q1) = q1:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (pi q0 q1))).symm).trans (p6 q1)
  have pl : forall (q0 q1:G), ((q1 ◇ q1) ◇ q1) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q1) ◇ (((q0 ◇ q0) ◇ q1) ◇ q1))) (cg (fun t => t ◇ q1) (pk q0 q1))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (pk q0 q1)))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (pk q0 q1))).symm).trans (((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q1) ◇ (((q0 ◇ q0) ◇ q1) ◇ q1))) (cg (fun t => t ◇ q1) (cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (pk q0 q1)))).symm).trans (p0 q1 ((q0 ◇ q0) ◇ q1)))
  have pm : forall (q1 q2 q0:G), (q2 ◇ (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ (q2 ◇ q1)))) = ((q1 ◇ q1) ◇ q1):=by
    intro q1 q2 q0
    exact ((((cg (fun t => q2 ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (pf q0 q1)))))).trans (cg (fun t => q2 ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q2 ◇ t) (pj q1 q1)))))).trans (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q1 ◇ (q2 ◇ q1))) (pf q0 q1)))).symm).trans ((((cg (fun t => q2 ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (pd q0 (q1 ◇ (q0 ◇ q0)))))))).symm).trans (pc q1 (q0 ◇ q0) (q1 ◇ (q0 ◇ q0)) q2)).trans (pf q0 q1))
  have pn : forall (q0 q1 q2:G), (q1 ◇ (q2 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q2)))) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q1 ◇ q2)) (pi q0 q2)))).symm).trans ((h q2 q1 q2).symm)
  have po : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ ((q1 ◇ q2) ◇ (q0 ◇ q0)))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => (q1 ◇ q2) ◇ t) (pi q0 q2)))).symm).trans ((h q1 q2 q2).symm)
  have pp : forall (q0 q1:G), (((q0 ◇ q0) ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (cg (fun t => t ◇ q1) (pi q0 q1))).symm).trans (p9 q1)
  have pq : forall (q0 q1 q2:G), (((q1 ◇ q1) ◇ q2) ◇ ((q0 ◇ q0) ◇ q2)) = (q2 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q1 ◇ q1) ◇ q2) ◇ t) (cg (fun t => t ◇ q2) (pi q0 q2))).symm).trans (pp q1 q2)
  have pr : forall (q0 q1:G), ((q1 ◇ q1) ◇ ((q0 ◇ q0) ◇ q0)) = ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (p9 q0)).symm).trans (pl q1 ((q0 ◇ q0) ◇ q0))).symm
  have ps : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ ((q0 ◇ q0) ◇ q1)) = ((q1 ◇ q1) ◇ ((q0 ◇ q0) ◇ q1)):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q1)) (pq q0 q0 q1)).symm).trans (pl q2 ((q0 ◇ q0) ◇ q1))).symm
  have pt : forall (q0:G), (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0) = ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)):=by
    intro q0
    exact ((cg (fun t => ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ t) (p7 q0)).symm).trans (pd q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))
  have pu : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) = ((q1 ◇ q1) ◇ ((q0 ◇ q0) ◇ q1)):=by
    intro q0 q1 q2
    exact (((ps q0 q1 q2).symm).trans (((cg (fun t => (q2 ◇ q2) ◇ t) (cg (fun t => t ◇ q1) (pi q0 q1))).symm).trans (pr q1 q2))).symm
  have pv : forall (q0 q1:G), (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q1) = ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q1) (cg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (pi q0 q1))).symm).trans (pt q1)
  have pw : forall (q0 q1:G), ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) = (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)):=by
    intro q0 q1
    exact (((((((cg (fun t => ((((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1))) ◇ q1) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ t) (pv q0 q1))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)))) (cg (fun t => t ◇ q1) (pq q1 q0 ((q1 ◇ q1) ◇ q1))))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)))) (cg (fun t => t ◇ q1) (pq q1 q1 q1)))).trans (cg (fun t => ((q1 ◇ q1) ◇ q1) ◇ t) (pq q1 q0 ((q1 ◇ q1) ◇ q1)))).trans (cg (fun t => ((q1 ◇ q1) ◇ q1) ◇ t) (pq q1 q1 q1))).symm).trans (((cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q1))) (cg (fun t => t ◇ q1) (cg (fun t => ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ t) (pv q0 q1)))).symm).trans (p0 q1 ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1))))).symm
  have px : forall (q0 q1:G), (q1 ◇ (q0 ◇ (((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) (pf q1 (q0 ◇ q1)))).symm).trans ((h q0 q1 q1).symm)
  have py : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q2)))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q1 ◇ q2)) (pi q0 (q1 ◇ q2))))).symm).trans (px q1 q2)
  have pz : forall (q0 q1 q2:G), ((q2 ◇ (q0 ◇ (q2 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))))) ◇ q2) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => (q2 ◇ (q0 ◇ (q2 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))))) ◇ t) (pc q0 q1 q2 q2)).symm).trans (((cg (fun t => t ◇ (q2 ◇ (q2 ◇ (q0 ◇ (q2 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))))))) (cg (fun t => t ◇ (q0 ◇ (q2 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))))) (pc q0 q1 q2 q2))).symm).trans (p0 (q0 ◇ (q2 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1))))) q2))
  have p10 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ (q2 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))))) = ((q2 ◇ q2) ◇ q2):=by
    intro q0 q1 q2
    exact (((((cg (fun t => t ◇ ((q2 ◇ (q0 ◇ (q2 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))))) ◇ ((q2 ◇ (q0 ◇ (q2 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))))) ◇ q2))) (cg (fun t => t ◇ q2) (pz q0 q1 q2))).trans (cg (fun t => (q2 ◇ q2) ◇ t) (cg (fun t => (q2 ◇ (q0 ◇ (q2 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))))) ◇ t) (pz q0 q1 q2)))).trans (cg (fun t => (q2 ◇ q2) ◇ t) (pz q0 q1 q2))).symm).trans (((cg (fun t => t ◇ ((q2 ◇ (q0 ◇ (q2 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))))) ◇ ((q2 ◇ (q0 ◇ (q2 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))))) ◇ q2))) (cg (fun t => t ◇ q2) (cg (fun t => (q2 ◇ (q0 ◇ (q2 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))))) ◇ t) (pz q0 q1 q2)))).symm).trans (p0 q2 (q2 ◇ (q0 ◇ (q2 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1))))))))).symm
  have p11 : forall (q0 q1 q2:G), ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q2)) = (((q2 ◇ q2) ◇ q2) ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ ((q1 ◇ q1) ◇ q2)) (pi q0 q2)).symm).trans ((pu q1 q2 q0).symm)).trans (pw q2 q2)
  have p12 : forall (q0 q1 q2:G), (((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ (q2 ◇ q2)) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ t) (cg (fun t => q2 ◇ t) ((h q2 (q1 ◇ q1) q0).symm))).symm).trans (py q1 q2 ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)))
  have p13 : forall (q0 q1 q2 q3:G), ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) = (((q2 ◇ q2) ◇ q2) ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact (((((((cg (fun t => t ◇ (((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)))) (cg (fun t => q2 ◇ t) (ph q2 q3))).trans (cg (fun t => t ◇ (((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)))) (pf q3 q2))).trans (pf ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ((q2 ◇ q2) ◇ q2))).trans (cg (fun t => t ◇ ((q2 ◇ q2) ◇ q2)) (pq q2 q2 q2))).trans (p11 q2 q2 q2)).symm).trans (((cg (fun t => t ◇ (((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)))) (cg (fun t => t ◇ ((q3 ◇ q3) ◇ (q2 ◇ q2))) (p12 q0 q1 q2))).symm).trans (p12 (q2 ◇ q2) q3 ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0))))).symm
  have p14 : forall (q0 q1 q2:G), (((q1 ◇ q1) ◇ q0) ◇ ((q2 ◇ q0) ◇ q2)) = (q2 ◇ q0):=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q1 ◇ q1) ◇ q0) ◇ t) (cg (fun t => (q2 ◇ q0) ◇ t) (p12 q0 q1 q2))).symm).trans (po q2 (q2 ◇ q0) ((q1 ◇ q1) ◇ q0))
  have p15 : forall (q0 q1 q2:G), ((q0 ◇ (q0 ◇ q1)) ◇ q1) = (((q2 ◇ q2) ◇ q1) ◇ q0):=by
    intro q0 q1 q2
    exact (((cg (fun t => ((q2 ◇ q2) ◇ q1) ◇ t) (p0 q1 q0)).symm).trans (p14 q1 q2 (q0 ◇ (q0 ◇ q1)))).symm
  have p16 : forall (q0 q1 q2:G), (((q2 ◇ q2) ◇ q1) ◇ q0) = (((q0 ◇ q0) ◇ q1) ◇ q0):=by
    intro q0 q1 q2
    exact ((p15 q0 q1 q2).symm).trans (p15 q0 q1 q0)
  have p17 : forall (q0 q1:G), (((q0 ◇ q0) ◇ q1) ◇ q0) = ((q0 ◇ (q0 ◇ q1)) ◇ q1):=by
    intro q0 q1
    exact ((p16 q0 q1 q1).symm).trans (((cg (fun t => t ◇ q0) ((pl q0 q1).symm)).symm).trans ((p15 q0 q1 q0).symm))
  have p18 : forall (q0 q1:G), ((q1 ◇ (q1 ◇ q0)) ◇ q0) = (((q0 ◇ q0) ◇ q0) ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ q1) (pm q0 (q1 ◇ q1) q0)).symm).trans (p17 q1 (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ ((q1 ◇ q1) ◇ q0))))).trans ((((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ ((q1 ◇ q1) ◇ q0)))) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (pj q1 q0))))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ ((q1 ◇ q1) ◇ q0)))) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (pk q0 q0))))).trans (cg (fun t => (q1 ◇ (q1 ◇ q0)) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (pj q1 q0)))).trans (cg (fun t => (q1 ◇ (q1 ◇ q0)) ◇ t) (pk q0 q0)))).symm
  have p19 : forall (q0 q1:G), (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ q1) = ((q1 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact (((pf (q1 ◇ q0) q1).symm).trans ((((cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ((h q1 q1 q0).symm)).symm).trans (p18 ((q1 ◇ q0) ◇ (q1 ◇ q0)) q1)).trans ((cg (fun t => t ◇ q1) (cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) (ph (q1 ◇ q0) (q1 ◇ q0)))).trans (cg (fun t => t ◇ q1) (ph (q1 ◇ q0) (q1 ◇ q0)))))).symm
  have p1a : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ (q1 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact (((pq q2 q1 q1).symm).trans ((((cg (fun t => t ◇ ((q2 ◇ q2) ◇ q1)) (p19 q0 q1)).symm).trans (p13 q1 q2 ((q1 ◇ q0) ◇ (q1 ◇ q0)) q0)).trans ((((cg (fun t => t ◇ (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))) (cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) (ph (q1 ◇ q0) (q1 ◇ q0)))).trans (cg (fun t => t ◇ (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))) (ph (q1 ◇ q0) (q1 ◇ q0)))).trans (cg (fun t => ((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ t) (ph (q1 ◇ q0) (q1 ◇ q0)))).trans (ph (q1 ◇ q0) (q1 ◇ q0))))).symm
  have p1b : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ (q1 ◇ q0)) = ((q1 ◇ q0) ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2
    exact (((cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => q2 ◇ t) (po q1 q2 (q1 ◇ q0)))).symm).trans ((((cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => (q2 ◇ (q1 ◇ q0)) ◇ t) (p1a q0 q1 q0)))))).symm).trans (p10 q2 (q1 ◇ q0) (q1 ◇ q0))).trans (cg (fun t => t ◇ (q1 ◇ q0)) (p1a q0 q1 ((q1 ◇ q0) ◇ (q1 ◇ q0)))))).symm
  have p1c : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ (q2 ◇ q2)) = ((q1 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact ((p1b q0 q1 q2).symm).trans (p1b q0 q1 q0)
  have p1d : forall (q0 q2 q1 q3:G), ((q2 ◇ q0) ◇ (q0 ◇ q0)) = ((q0 ◇ q0) ◇ (q2 ◇ q0)):=by
    intro q0 q2 q1 q3
    exact (((cg (fun t => t ◇ (q2 ◇ q0)) (pq q1 q1 q0)).symm).trans ((((cg (fun t => (((q1 ◇ q1) ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ t) (p14 q0 q1 q2)).symm).trans (p1b ((q2 ◇ q0) ◇ q2) ((q1 ◇ q1) ◇ q0) q3)).trans ((cg (fun t => t ◇ (q3 ◇ q3)) (p14 q0 q1 q2)).trans (p1c q0 q2 q3)))).symm
  have p1e : forall (q0 q1 q2 q3:G), ((q1 ◇ q0) ◇ (q2 ◇ q2)) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2 q3
    exact (p1c q0 q1 q2).trans (p1d q0 q1 ((q1 ◇ q0) ◇ (q0 ◇ q0)) ((q1 ◇ q0) ◇ (q0 ◇ q0)))
  exact (calc
    x = x:=rfl
    _ = (y ◇ (x ◇ ((y ◇ x) ◇ (z ◇ z)))):=((cg (fun t => y ◇ t) (cg (fun t => x ◇ t) (p1e x y z ((y ◇ x) ◇ (z ◇ z))))).trans (pn x y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6678_to_6697 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6678_to_6697
