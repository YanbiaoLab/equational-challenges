-- Equation19010 → Equation42706
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ ((z ◇ x) ◇ (y ◇ z))
-- Conclusion: x ◇ y = x ◇ (z ◇ ((y ◇ y) ◇ z))
-- Original submission SHA-256: 43b5be84e8f34bfa013ae86ac8349a9bafde5769307489027fb40332596f3f72
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ ((z ◇ x) ◇ (y ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = x ◇ (z ◇ ((y ◇ y) ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (x y z:G), ((y ◇ x) ◇ ((z ◇ x) ◇ (y ◇ z))) = ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have p1 : forall (x y z:G), ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) = x:=by
    intro x y z
    exact ((h x x x).trans (p0 x x x)).symm
  have p2 : forall (q0 q1 q2 q3:G), (((q1 ◇ q0) ◇ q3) ◇ ((((q2 ◇ q0) ◇ (q1 ◇ q2)) ◇ q3) ◇ q0)) = q3:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => ((q1 ◇ q0) ◇ q3) ◇ t) (cg (fun t => (((q2 ◇ q0) ◇ (q1 ◇ q2)) ◇ q3) ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h q3 (q1 ◇ q0) ((q2 ◇ q0) ◇ (q1 ◇ q2))).symm)
  have p3 : forall (q0 q1 q2 q3:G), ((q3 ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))) ◇ (q0 ◇ (q3 ◇ (q1 ◇ q0)))) = ((q2 ◇ q0) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (q3 ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))) ◇ t) (cg (fun t => t ◇ (q3 ◇ (q1 ◇ q0))) ((h q0 q1 q2).symm))).symm).trans ((h ((q2 ◇ q0) ◇ (q1 ◇ q2)) q3 (q1 ◇ q0)).symm)
  have p4 : forall (q0 q1 q2:G), (q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))) = ((q2 ◇ q0) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q0 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))) ((h q0 q1 q2).symm)).symm).trans (p3 q0 q1 q2 (q1 ◇ q0))
  have p5 : forall (q0 q1 q2:G), ((q2 ◇ q0) ◇ (q1 ◇ q2)) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact ((p4 q0 q1 q2).symm).trans (p4 q0 q1 q0)
  have p6 : forall (x y z q0 q1 q2:G), ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ x))) = x:=by
    intro x y z q0 q1 q2
    exact ((h x y x).trans (cg (fun t => (y ◇ x) ◇ t) (p5 x y x))).symm
  have p7 : forall (q0 q1 q2:G), (q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact (p4 q0 q1 q2).trans (p5 q0 q1 q2)
  have p8 : forall (q0 q1 q3 q2:G), ((((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ q3) ◇ q0) = ((q3 ◇ q3) ◇ ((q1 ◇ q0) ◇ q3)):=by
    intro q0 q1 q3 q2
    exact ((cg (fun t => t ◇ q0) (cg (fun t => t ◇ q3) (p5 q0 q1 q2))).symm).trans (((cg (fun t => (((q2 ◇ q0) ◇ (q1 ◇ q2)) ◇ q3) ◇ t) ((h q0 q1 q2).symm)).symm).trans (p5 q3 (q1 ◇ q0) ((q2 ◇ q0) ◇ (q1 ◇ q2))))
  have p9 : forall (q0 q1 q2 q3:G), (((q1 ◇ q2) ◇ q3) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) = ((q3 ◇ q3) ◇ ((q2 ◇ q0) ◇ q3)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => ((q1 ◇ q2) ◇ q3) ◇ t) (p5 q0 q1 q2)).symm).trans (p5 q3 (q2 ◇ q0) (q1 ◇ q2))
  have pa : forall (q0 q1 q2:G), ((((q1 ◇ q0) ◇ q0) ◇ ((q2 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q2))) ◇ q0) = ((q2 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => (((q1 ◇ q0) ◇ q0) ◇ ((q2 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q2))) ◇ t) ((h q0 q1 (q1 ◇ q0)).symm)).symm).trans (p3 (q1 ◇ q0) q1 q2 ((q1 ◇ q0) ◇ q0))
  have pb : forall (q0 q1:G), (((q1 ◇ q1) ◇ ((q1 ◇ (q0 ◇ q1)) ◇ q1)) ◇ q1) = ((q1 ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q1) (p5 q1 (q1 ◇ (q0 ◇ q1)) (q0 ◇ q1))).symm).trans (pa q1 q0 q1)
  have pc : forall (q0 q1 q2:G), ((q2 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q2)) = ((q0 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact ((((cg (fun t => t ◇ q0) (p9 (q1 ◇ q0) q1 q0 q0)).trans (pb q1 q0)).symm).trans (((cg (fun t => t ◇ q0) (cg (fun t => ((q1 ◇ q0) ◇ q0) ◇ t) (p5 (q1 ◇ q0) q1 q2))).symm).trans (pa q0 q1 q2))).symm
  have pd : forall (q0 q1 q2:G), (((q0 ◇ q0) ◇ (q2 ◇ q0)) ◇ (q2 ◇ (q1 ◇ q0))) = ((q1 ◇ (q2 ◇ q1)) ◇ (q2 ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q2 ◇ (q1 ◇ q0))) (p5 q0 q2 q1)).symm).trans (pc q1 q2 (q1 ◇ q0))
  have pe : forall (q0 q1:G), ((q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => t ◇ (q1 ◇ (q0 ◇ q0))) (p1 q0 q0 q0))).symm).trans ((h ((q0 ◇ q0) ◇ (q0 ◇ q0)) q1 (q0 ◇ q0)).symm)
  have pf : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ (((q1 ◇ (q0 ◇ q0)) ◇ q0) ◇ q2)) = ((q2 ◇ q2) ◇ ((q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q2)):=by
    intro q0 q1 q2
    exact ((p9 q0 q0 (q1 ◇ (q0 ◇ q0)) q2).symm).trans (((cg (fun t => ((q0 ◇ (q1 ◇ (q0 ◇ q0))) ◇ q2) ◇ t) (pe q0 q1)).symm).trans (p5 q2 (q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (q0 ◇ (q1 ◇ (q0 ◇ q0)))))
  have pg : forall (q0:G), ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0
    exact (((cg (fun t => (q0 ◇ q0) ◇ t) (p8 q0 q0 q0 q0)).symm).trans (pf q0 (q0 ◇ q0) q0)).trans (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ q0) (p6 q0 q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))))
  have ph : forall (q0 q1 q2 q3:G), (((q1 ◇ q2) ◇ q3) ◇ ((q0 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0))) = ((q3 ◇ q3) ◇ ((q2 ◇ (q1 ◇ q0)) ◇ q3)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => ((q1 ◇ q2) ◇ q3) ◇ t) (pc q0 q1 q2)).symm).trans (p5 q3 (q2 ◇ (q1 ◇ q0)) (q1 ◇ q2))
  have pi : forall (q0 q1 q2 q3:G), ((q3 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ (q0 ◇ (q3 ◇ (q1 ◇ q0)))) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ (q0 ◇ (q3 ◇ (q1 ◇ q0)))) (cg (fun t => q3 ◇ t) (p5 q0 q1 q2))).symm).trans ((p3 q0 q1 q2 q3).trans (p5 q0 q1 q2))
  have pj : forall (q0 q1 q2 q3:G), ((q2 ◇ q2) ◇ ((((q3 ◇ q3) ◇ (q0 ◇ q3)) ◇ q1) ◇ q2)) = ((q3 ◇ q2) ◇ ((q1 ◇ q1) ◇ ((q0 ◇ q3) ◇ q1))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => (q3 ◇ q2) ◇ t) (p8 q3 q0 q1 q0)).symm).trans (p5 q2 (((q3 ◇ q3) ◇ (q0 ◇ q3)) ◇ q1) q3)).symm
  have pk : forall (q0 q1:G), ((q0 ◇ q1) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) = ((q1 ◇ q1) ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact (((pj q0 q0 q1 q0).symm).trans (pf q0 (q0 ◇ q0) q1)).trans (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (p6 q0 q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))))
  have pl : forall (q0:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = (q0 ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))):=by
    intro q0
    exact (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (pg q0)).symm).trans (pc ((q0 ◇ q0) ◇ q0) (q0 ◇ q0) (q0 ◇ q0))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (p6 q0 (q0 ◇ q0) (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))))
  have pm : forall (q0:G), ((q0 ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0) = (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))):=by
    intro q0
    exact ((cg (fun t => (q0 ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) ◇ t) (p6 q0 q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))).symm).trans ((((cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (pl q0)).symm).trans (pc (q0 ◇ q0) (q0 ◇ q0) ((q0 ◇ q0) ◇ (q0 ◇ q0)))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (p6 q0 q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))))
  have pn : forall (q0 q1 q2 q3:G), (q1 ◇ ((((q1 ◇ q1) ◇ (q2 ◇ q1)) ◇ ((q0 ◇ q1) ◇ (q2 ◇ q0))) ◇ q1)) = ((q0 ◇ q1) ◇ (q2 ◇ q0)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ (q2 ◇ q0))) (p5 q1 q2 q3)))).symm).trans (((cg (fun t => t ◇ ((((q3 ◇ q1) ◇ (q2 ◇ q3)) ◇ ((q0 ◇ q1) ◇ (q2 ◇ q0))) ◇ q1)) ((h q1 q2 q0).symm)).symm).trans (p2 q1 q2 q3 ((q0 ◇ q1) ◇ (q2 ◇ q0))))
  have po : forall (q0 q1 q2 q3:G), (((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ ((q3 ◇ (q1 ◇ q2)) ◇ ((q2 ◇ q0) ◇ q3))) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ ((q3 ◇ (q1 ◇ q2)) ◇ ((q2 ◇ q0) ◇ q3))) (p5 q0 q1 q2)).symm).trans ((h (q1 ◇ q2) (q2 ◇ q0) q3).symm)
  have pp : forall (q0 q1 q2 q3:G), ((q3 ◇ (q1 ◇ q2)) ◇ (((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ (q3 ◇ (q2 ◇ q0)))) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (q3 ◇ (q1 ◇ q2)) ◇ t) (cg (fun t => t ◇ (q3 ◇ (q2 ◇ q0))) (p5 q0 q1 q2))).symm).trans ((h (q1 ◇ q2) q3 (q2 ◇ q0)).symm)
  have pq : forall (q0 q1 q2:G), (((q1 ◇ (q2 ◇ q0)) ◇ (q2 ◇ (q0 ◇ q1))) ◇ (q2 ◇ q0)) = (q2 ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q1 ◇ (q2 ◇ q0)) ◇ (q2 ◇ (q0 ◇ q1))) ◇ t) (po q1 q2 q0 q1)).symm).trans (pp q1 q2 (q0 ◇ q1) (q1 ◇ (q2 ◇ q0)))
  have pr : forall (q0 q1 q2:G), (((q0 ◇ (q2 ◇ q0)) ◇ (q2 ◇ q0)) ◇ (q2 ◇ (q1 ◇ (q2 ◇ q0)))) = ((q1 ◇ (q2 ◇ q1)) ◇ (q2 ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q2 ◇ (q1 ◇ (q2 ◇ q0)))) (pc q0 q2 q1)).symm).trans (pc q1 q2 (q1 ◇ (q2 ◇ q0)))
  have ps : forall (q0 q1:G), ((q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ ((q0 ◇ q0) ◇ q0)) = (q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) (p6 q0 q1 ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0)))))).symm).trans ((((cg (fun t => (((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p6 q0 q1 q0 q0 q0 q0))).symm).trans (pr (q1 ◇ q0) (q1 ◇ q0) (q0 ◇ q0))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) (p6 q0 q1 ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))))))
  have pt : forall (q0 q2 q1:G), ((q2 ◇ q2) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q2) ◇ q2)) = q2:=by
    intro q0 q2 q1
    exact ((p5 q2 (((q0 ◇ q0) ◇ q0) ◇ q2) (q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0)))).symm).trans (((cg (fun t => ((q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ q2) ◇ t) (cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ q2) ◇ t) (ps q0 q1))).symm).trans ((h q2 (q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ((q0 ◇ q0) ◇ q0)).symm))
  have pu : forall (q1 q0:G), (q1 ◇ ((q1 ◇ q1) ◇ q1)) = q1:=by
    intro q1 q0
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (pt q0 q1 ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1)))))).symm).trans ((((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1)) ◇ t) (pt q0 q1 q0)))).symm).trans (pn q1 q1 (((q0 ◇ q0) ◇ q0) ◇ q1) q0)).trans (pt q0 q1 ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1))))
  have pv : forall (q1 q0:G), (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)) = q1:=by
    intro q1 q0
    exact ((cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => (q1 ◇ q1) ◇ t) (pt q0 q1 ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1))))).symm).trans ((((cg (fun t => ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1))) ◇ t) (cg (fun t => q1 ◇ t) (pt q0 q1 q0))).symm).trans (pi q1 (((q0 ◇ q0) ◇ q0) ◇ q1) q0 (q1 ◇ q1))).trans (pt q0 q1 ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1))))
  have pw : forall (q1 q0:G), ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) = (q1 ◇ q1):=by
    intro q1 q0
    exact (((cg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (cg (fun t => q1 ◇ t) (pt q0 q1 q0))).symm).trans (ps q1 (((q0 ◇ q0) ◇ q0) ◇ q1))).trans (cg (fun t => q1 ◇ t) (pt q0 q1 ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1))))
  have px : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q0 ◇ q1)) = ((q0 ◇ q1) ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact (((cg (fun t => (q0 ◇ q1) ◇ t) (pw q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))).symm).trans (pk q0 q1)).symm
  have py : forall (q0:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0) = q0:=by
    intro q0
    exact (((cg (fun t => t ◇ q0) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ q0) (pu q0 q0)))).symm).trans (pb (q0 ◇ q0) q0)).trans ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (pu q0 (q0 ◇ ((q0 ◇ q0) ◇ q0)))).trans (pu q0 (q0 ◇ ((q0 ◇ q0) ◇ q0))))
  have pz : forall (q0:G), ((q0 ◇ q0) ◇ q0) = (q0 ◇ (q0 ◇ (q0 ◇ q0))):=by
    intro q0
    exact (((cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (py q0)))).symm).trans ((((cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0)) (py q0)))).symm).trans (p7 q0 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q0)).trans (cg (fun t => (q0 ◇ q0) ◇ t) (py q0)))).symm
  have p10 : forall (q0:G), ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact (((cg (fun t => q0 ◇ t) (pu q0 (q0 ◇ ((q0 ◇ q0) ◇ q0)))).symm).trans (((cg (fun t => t ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) (pv q0 q0)).symm).trans (pc q0 q0 ((q0 ◇ q0) ◇ q0)))).symm
  have p11 : forall (q0 q1:G), (((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1) ◇ q1) = q1:=by
    intro q0 q1
    exact ((cg (fun t => ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1) ◇ t) (pt q0 q1 q0)).symm).trans ((h q1 (((q0 ◇ q0) ◇ q0) ◇ q1) q1).symm)
  have p12 : forall (q0:G), (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0
    exact ((ps q0 q0).symm).trans (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (pu q0 q0))).symm).trans (pq q0 q0 (q0 ◇ q0)))
  have p13 : forall (q0 q1:G), ((q0 ◇ (q0 ◇ q0)) ◇ q0) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ q0) (cg (fun t => q0 ◇ t) (pw q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))))).symm).trans (pm q0)).trans (p12 q0)
  have p14 : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ q1)) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q1)) (cg (fun t => q1 ◇ t) (pw q0 q0))).symm).trans (pc ((q0 ◇ q0) ◇ q0) (q0 ◇ q0) q1)).trans (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (pw q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (pv q0 (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))))).trans (cg (fun t => q0 ◇ t) (pw q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))))
  have p15 : forall (q0:G), ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))) = q0:=by
    intro q0
    exact (((((cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (pc q0 q0 (q0 ◇ q0))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (p10 q0))).trans (p6 q0 q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))).symm).trans ((((cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (p14 q0 (q0 ◇ q0)))).symm).trans (p13 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q0)).trans ((cg (fun t => t ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (p14 q0 (q0 ◇ q0))).trans (cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (p14 q0 (q0 ◇ q0)))))).symm
  have p16 : forall (q0 q1:G), ((q1 ◇ q1) ◇ (((q0 ◇ q0) ◇ q0) ◇ q1)) = (((q0 ◇ q0) ◇ q1) ◇ q0):=by
    intro q0 q1
    exact (((cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (pv q0 q0)).symm).trans (p5 q1 ((q0 ◇ q0) ◇ q0) (q0 ◇ q0))).symm
  have p17 : forall (q0 q1 q2:G), ((((q0 ◇ q0) ◇ q1) ◇ q2) ◇ (q0 ◇ q0)) = ((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => (((q0 ◇ q0) ◇ q1) ◇ q2) ◇ t) (pw q0 q0)).symm).trans (p9 q0 (q0 ◇ q0) q1 q2)
  have p18 : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ ((q1 ◇ (q0 ◇ q0)) ◇ q2)) = (((q0 ◇ q1) ◇ q2) ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact (((cg (fun t => ((q0 ◇ q1) ◇ q2) ◇ t) (p10 q0)).symm).trans (ph q0 q0 q1 q2)).symm
  have p19 : forall (q0 q1 q2:G), ((((q0 ◇ (q0 ◇ q0)) ◇ q1) ◇ q2) ◇ q0) = ((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => (((q0 ◇ (q0 ◇ q0)) ◇ q1) ◇ q2) ◇ t) (p6 q0 q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))).symm).trans (((cg (fun t => (((q0 ◇ (q0 ◇ q0)) ◇ q1) ◇ q2) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p13 q0 q0))).symm).trans (p9 q0 (q0 ◇ (q0 ◇ q0)) q1 q2))
  have p1a : forall (q0 q1:G), (((q0 ◇ (q0 ◇ q0)) ◇ q1) ◇ (q0 ◇ q0)) = ((q0 ◇ q1) ◇ q0):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ q0) (cg (fun t => t ◇ q1) (p15 q0))).symm).trans (p19 q0 (q0 ◇ (q0 ◇ q0)) q1)).trans ((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (p13 q0 ((q0 ◇ (q0 ◇ q0)) ◇ q0)))).trans (p18 q0 (q0 ◇ q0) q1))).symm
  have p1b : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q1 ◇ (q1 ◇ (q1 ◇ q1)))) = ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q0) ◇ t) (pz q1)).symm).trans (p5 q0 (q1 ◇ q1) q1)
  have p1c : forall (q0 q1:G), (((q0 ◇ q0) ◇ q1) ◇ ((q0 ◇ q0) ◇ q0)) = ((q0 ◇ q1) ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p6 q0 q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))))).symm).trans ((((cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p5 q0 q0 q0)))).symm).trans (p1b q1 (q0 ◇ q0))).trans ((p18 q0 (q0 ◇ q0) q1).trans (p1a q0 q1)))
  have p1d : forall (q0 q1:G), (((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ (((q0 ◇ q0) ◇ q1) ◇ q0)) ◇ (((q0 ◇ q0) ◇ q1) ◇ q0)) = ((q1 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ q1) (pw q1 ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)))).symm).trans ((((cg (fun t => ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) ◇ t) (pt q0 q1 q0)).symm).trans (pd q1 (((q0 ◇ q0) ◇ q0) ◇ q1) (q1 ◇ q1))).trans ((cg (fun t => t ◇ ((q1 ◇ q1) ◇ (((q0 ◇ q0) ◇ q0) ◇ q1))) (cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ q1) ◇ t) (p16 q0 q1))).trans (cg (fun t => ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ (((q0 ◇ q0) ◇ q1) ◇ q0)) ◇ t) (p16 q0 q1))))).symm
  have p1e : forall (q0 q1:G), ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ (((q0 ◇ q0) ◇ q1) ◇ q0)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ q1) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (pv q0 q0))).symm).trans ((h q1 ((q0 ◇ q0) ◇ q0) (q0 ◇ q0)).symm)
  have p1f : forall (q0 q1:G), (q1 ◇ (((q0 ◇ q0) ◇ q1) ◇ q0)) = ((q1 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q1) ◇ q0)) (p1e q0 q1)).symm).trans (p1d q0 q1)
  have p1g : forall (q0 q1:G), (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0) = ((q1 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact ((((((((((cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (cg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (p1c q1 q1)))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (p1c q1 q1)))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (p1f q0 ((q1 ◇ q1) ◇ q1)))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (cg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (p1c q1 q1)))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (p1c q1 q1))).trans (p1f q0 ((q1 ◇ q1) ◇ q1))).trans (cg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (p1c q1 q1))).trans (p1c q1 q1)).symm).trans (((cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (p1f q0 ((q1 ◇ q1) ◇ q1)))).symm).trans (p11 q1 (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)))).symm
  have p1h : forall (q0 q1:G), (((q0 ◇ q0) ◇ q0) ◇ (q1 ◇ q1)) = q1:=by
    intro q0 q1
    exact (((cg (fun t => t ◇ (q1 ◇ q1)) (p1g q1 q0)).symm).trans (p17 q1 ((q0 ◇ q0) ◇ q0) q1)).trans (pt q0 q1 ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1)))
  have p1i : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q0) ◇ q0)) = q1:=by
    intro q0 q1
    exact (((py q1).symm).trans ((((cg (fun t => ((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ t) (p1h q0 q1)).symm).trans (px ((q0 ◇ q0) ◇ q0) (q1 ◇ q1))).trans ((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (p1h q0 q1)).trans (cg (fun t => q1 ◇ t) (p1c q0 q0))))).symm
  have p1j : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q0) ◇ q1)) = q0:=by
    intro q0 q1
    exact (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q1)) (p1i q0 q1)).symm).trans (pc q0 (q0 ◇ q0) q1)).trans ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (p1i q0 q0)).trans (p1i q0 q0))
  exact (calc
    (x ◇ y) = (x ◇ y):=rfl
    _ = (x ◇ (z ◇ ((y ◇ y) ◇ z))):=(cg (fun t => x ◇ t) (p1j y z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19010_to_42706 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19010_to_42706
