-- Equation6732 → Equation53146
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ ((z ◇ x) ◇ (y ◇ z)))
-- Conclusion: x ◇ y = (((x ◇ x) ◇ y) ◇ y) ◇ x
-- Original submission SHA-256: bc50abdd928729eedad28085e639b474ca241bad5d55405b47bdd53687a7ba24
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((z ◇ x) ◇ (y ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = (((x ◇ x) ◇ y) ◇ y) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have p0:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ ((b ◇ a) ◇ b)) ◇ t) ((h ((b ◇ a) ◇ b) b a).symm)).symm).trans ((h b (a ◇ ((b ◇ a) ◇ b)) (b ◇ a)).symm)
  have p1:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p0 a a))).symm).trans ((h ((a ◇ a) ◇ a) (a ◇ a) a).symm)
  have p2:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => a ◇ t) (p1 a))).symm).trans ((h a ((a ◇ a) ◇ a) a).symm)
  have p3:=fun (a b c:G)=>by
    exact ((h a b c).symm).trans (h a a a)
  have p4:=fun (a b c d:G)=>by
    exact ((cg (fun t => c ◇ t) (cg (fun t => (a ◇ ((b ◇ a) ◇ (d ◇ b))) ◇ t) (cg (fun t => t ◇ (c ◇ d)) ((h a d b).symm)))).symm).trans ((h (a ◇ ((b ◇ a) ◇ (d ◇ b))) c d).symm)
  have p5:=fun (a:G)=>by
    exact ((p3 a a a).symm).trans ((h a a a).symm)
  have p6:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ ((a ◇ a) ◇ a))) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p2 a))).symm).trans (((cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ ((a ◇ a) ◇ a))) ◇ ((a ◇ a) ◇ a))) (cg (fun t => (a ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p2 a)))).symm).trans (p0 (a ◇ ((a ◇ a) ◇ a)) ((a ◇ a) ◇ a)))
  have p7:=fun (a:G)=>by
    exact (((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => (a ◇ ((a ◇ a) ◇ a)) ◇ t) (p6 a))).trans (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p0 a a))).symm).trans (((cg (fun t => t ◇ ((a ◇ ((a ◇ a) ◇ a)) ◇ (((a ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ ((a ◇ a) ◇ a))) ◇ (a ◇ ((a ◇ a) ◇ a))))) (p6 a)).symm).trans (p2 (a ◇ ((a ◇ a) ◇ a))))
  have p8:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (p7 a)).symm).trans (p1 a)
  have p9:=fun (a b c d:G)=>by
    exact ((cg (fun t => d ◇ t) (cg (fun t => c ◇ t) (cg (fun t => ((a ◇ ((b ◇ a) ◇ (d ◇ b))) ◇ c) ◇ t) ((h a d b).symm)))).symm).trans ((h c d (a ◇ ((b ◇ a) ◇ (d ◇ b)))).symm)
  have pa:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ a) ◇ b) ◇ (b ◇ (a ◇ ((b ◇ a) ◇ b)))) ◇ t) (cg (fun t => t ◇ (a ◇ ((b ◇ a) ◇ b))) (p0 a b))).symm).trans (((cg (fun t => t ◇ (((a ◇ ((b ◇ a) ◇ b)) ◇ ((b ◇ a) ◇ b)) ◇ (a ◇ ((b ◇ a) ◇ b)))) (cg (fun t => ((b ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ (a ◇ ((b ◇ a) ◇ b))) (p0 a b)))).symm).trans (p0 ((b ◇ a) ◇ b) (a ◇ ((b ◇ a) ◇ b))))
  have pb:=fun (a b c:G)=>by
    exact ((cg (fun t => c ◇ t) (cg (fun t => ((b ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ (c ◇ (a ◇ ((b ◇ a) ◇ b)))) (p0 a b)))).symm).trans ((h ((b ◇ a) ◇ b) c (a ◇ ((b ◇ a) ◇ b))).symm)
  have pc:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => a ◇ t) (p2 a)))).symm).trans (pb a a ((a ◇ a) ◇ a))
  have pd:=fun (a b c:G)=>by
    exact ((cg (fun t => (a ◇ ((b ◇ a) ◇ b)) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => (((b ◇ a) ◇ b) ◇ c) ◇ t) (p0 a b)))).symm).trans ((h c (a ◇ ((b ◇ a) ◇ b)) ((b ◇ a) ◇ b)).symm)
  have pe:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => (a ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => t ◇ a) (p2 a)))).symm).trans (pd a a (a ◇ ((a ◇ a) ◇ a)))
  have pf:=fun (a b c:G)=>by
    exact ((cg (fun t => ((c ◇ ((a ◇ c) ◇ (b ◇ a))) ◇ (c ◇ b)) ◇ t) (p9 c a (c ◇ b) b)).symm).trans ((h b ((c ◇ ((a ◇ c) ◇ (b ◇ a))) ◇ (c ◇ b)) c).symm)
  have pg:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ (a ◇ ((b ◇ a) ◇ (c ◇ b)))) ◇ c)) (cg (fun t => (a ◇ ((b ◇ a) ◇ (c ◇ b))) ◇ t) (cg (fun t => t ◇ c) ((h a c b).symm)))).symm).trans (p0 (a ◇ ((b ◇ a) ◇ (c ◇ b))) c)
  have ph:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => ((a ◇ ((a ◇ a) ◇ a)) ◇ b) ◇ t) (p2 a)))).symm).trans ((h b ((a ◇ a) ◇ a) (a ◇ ((a ◇ a) ◇ a))).symm)
  have pi:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ b) ◇ t) (pc a)))).symm).trans ((h b ((a ◇ a) ◇ a) (((a ◇ a) ◇ a) ◇ (a ◇ a))).symm)
  have pj:=fun (a b:G)=>by
    exact (((cg (fun t => ((a ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => t ◇ (a ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ b) (p6 a))))).trans (cg (fun t => t ◇ (b ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ (a ◇ ((a ◇ a) ◇ a))))) (p0 a a))).symm).trans (((cg (fun t => t ◇ (b ◇ (((((a ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ ((a ◇ a) ◇ a))) ◇ (a ◇ ((a ◇ a) ◇ a))) ◇ b) ◇ (a ◇ ((a ◇ a) ◇ a))))) (cg (fun t => (a ◇ ((a ◇ a) ◇ a)) ◇ t) (p6 a))).symm).trans (pd (a ◇ ((a ◇ a) ◇ a)) (a ◇ ((a ◇ a) ◇ a)) b))
  have pk:=fun (a:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (p2 a))).symm).trans (((cg (fun t => a ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (a ◇ ((a ◇ a) ◇ a))) (pc a)))).symm).trans (pj a (((a ◇ a) ◇ a) ◇ (a ◇ a))))
  have pl:=fun (a:G)=>by
    exact ((cg (fun t => (((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ a) ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ a)) ◇ t) (cg (fun t => t ◇ a) (pk a))).symm).trans (((cg (fun t => t ◇ ((a ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ a)) ◇ a)) (cg (fun t => ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ a) ◇ t) (cg (fun t => t ◇ a) (pk a)))).symm).trans (p0 ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ a) a))
  have pm:=fun (a:G)=>by
    exact (((pk a).symm).trans ((((cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ a)) (pl a)).symm).trans (p7 ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ a))).trans (cg (fun t => ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ a) ◇ t) (pl a)))).symm
  have pn:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p7 b)))).symm).trans ((h a ((b ◇ b) ◇ b) b).symm)
  have po:=fun (a b:G)=>by
    exact (((cg (fun t => (a ◇ ((a ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a))) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ b) (p0 a a))))).trans (cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ ((a ◇ a) ◇ a)))) (cg (fun t => a ◇ t) (p0 a a)))).symm).trans (((cg (fun t => (a ◇ ((a ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a))) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ b) (pn ((a ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)) a))))).symm).trans (p9 ((a ◇ a) ◇ a) (a ◇ ((a ◇ a) ◇ a)) b (a ◇ ((a ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)))))
  have pp:=fun (a b:G)=>by
    exact (((cg (fun t => b ◇ t) (cg (fun t => ((a ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (p0 a a)))))).trans (cg (fun t => b ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (b ◇ (a ◇ a)))) (p0 a a)))).symm).trans ((((cg (fun t => b ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (b ◇ (a ◇ ((a ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)))))) (pn ((a ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)) a))).symm).trans (p4 ((a ◇ a) ◇ a) (a ◇ ((a ◇ a) ◇ a)) b (a ◇ ((a ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a))))).trans ((((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => ((a ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => t ◇ (a ◇ ((a ◇ a) ◇ a))) (cg (fun t => a ◇ t) (p0 a a))))).trans (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => ((a ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)) ◇ t) (p8 a)))).trans (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p0 a a)))).trans (p2 a)))
  have pq:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => ((a ◇ ((a ◇ a) ◇ a)) ◇ b) ◇ t) (p8 a)))).symm).trans ((h b (a ◇ a) (a ◇ ((a ◇ a) ◇ a))).symm)
  have pr:=fun (a:G)=>by
    exact ((((cg (fun t => a ◇ t) (cg (fun t => ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ a) ◇ t) (pl a))).trans (cg (fun t => a ◇ t) (pm a))).symm).trans (((cg (fun t => t ◇ (((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ a) ◇ ((((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ a) ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ a)) ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ a)))) (pl a)).symm).trans (p2 ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ a)))).symm
  have ps:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ a) (pr a)).symm).trans (pm a)
  have pt:=fun (a:G)=>by
    exact ((cg (fun t => ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))) ◇ t) (ps a)).symm).trans (((cg (fun t => t ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))) ◇ a)) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (ps a))).symm).trans (p0 (((a ◇ a) ◇ a) ◇ (a ◇ a)) a))
  have pu:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => ((a ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ a)) ◇ t) (p0 a a))).symm).trans (((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => ((a ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pe a)))).symm).trans (pq a ((a ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ a))))
  have pv:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (pu a)).symm).trans (ph a (a ◇ a))
  have pw:=fun (a:G)=>by
    exact (((cg (fun t => a ◇ t) (pv a)).symm).trans ((h ((a ◇ a) ◇ a) a a).symm)).symm
  have px:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ a) (pw a)).symm).trans (p7 a)
  have py:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ a) (pw a))).symm).trans (p1 a)
  have pz:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => a ◇ t) (pv a))).symm).trans ((h a (a ◇ ((a ◇ a) ◇ a)) (a ◇ a)).symm)
  have p10:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ (a ◇ a))) (cg (fun t => a ◇ t) (pw a))).symm).trans (pz a)
  have p11:=fun (a:G)=>by
    exact (((cg (fun t => ((a ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ t) (cg (fun t => t ◇ a) (cg (fun t => a ◇ t) (pv a)))).trans (cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ a)) (p1 a))).symm).trans (((cg (fun t => t ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ a)))) ◇ a)) (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ a)) (pv a))).symm).trans (pg ((a ◇ a) ◇ a) a a))
  have p12:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ a)) (pw a)).symm).trans (p11 a)
  have p13:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p12 a))).symm).trans ((h (a ◇ a) (a ◇ (a ◇ a)) a).symm)
  have p14:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p13 a))).symm).trans ((h (a ◇ a) (a ◇ a) a).symm)
  have p15:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ (a ◇ a)) ◇ t) (pw a)).symm).trans (p13 a)
  have p16:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p14 a)).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a)))) (cg (fun t => (a ◇ a) ◇ t) (p14 a))).symm).trans (p10 (a ◇ a)))
  have p17:=fun (a:G)=>by
    exact ((((((cg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a)))) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p16 a))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a)))) (cg (fun t => (a ◇ a) ◇ t) (p14 a)))).trans (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p14 a))).trans (p16 a)).symm).trans (((cg (fun t => t ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a)))) (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p16 a)))).symm).trans (p0 (a ◇ a) ((a ◇ a) ◇ (a ◇ a))))).symm
  have p18:=fun (a:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (p17 a))).symm).trans (p5 a)
  have p19:=fun (a:G)=>by
    exact ((((cg (fun t => t ◇ (a ◇ (a ◇ a))) (p15 a)).symm).trans (pw (a ◇ (a ◇ a)))).trans (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p15 a))).symm
  have p1a:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => a ◇ t) (p17 a)))).symm).trans (pf a a a)
  have p1b:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p15 a))).symm).trans ((((cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p15 a))).symm).trans (p15 (a ◇ (a ◇ a)))).trans (p15 a))
  have p1c:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ a))) (p1b a)).symm).trans (pw ((a ◇ (a ◇ a)) ◇ (a ◇ a)))).trans ((cg (fun t => ((a ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (p1b a)).trans (p1a a))
  have p1d:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (p19 a)).symm).trans (p1c a)
  have p1e:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ a)) (p19 a)).symm).trans (p1a a)
  have p1f:=fun (a:G)=>by
    exact (((((((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ (a ◇ (a ◇ a))) ◇ (a ◇ a))))) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1e a))))).trans (cg (fun t => (a ◇ ((a ◇ a) ◇ ((a ◇ (a ◇ a)) ◇ a))) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1e a))))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ (a ◇ a)) ◇ a))) (cg (fun t => a ◇ t) (py a)))).trans (cg (fun t => (a ◇ ((a ◇ a) ◇ a)) ◇ t) (py a))).trans (p0 a a)).symm).trans ((((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ (a ◇ (a ◇ a))) ◇ (a ◇ a))))) (cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ (a ◇ (a ◇ a))) ◇ (a ◇ a))))) (p1e a))).symm).trans (pa (a ◇ (a ◇ a)) (a ◇ a))).trans (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1e a)))).symm
  have p1g:=fun (a:G)=>by
    exact (((p1f a).symm).trans (px a)).symm
  have p1h:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p1f a)).symm).trans (p11 a)
  have p1i:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ a) (cg (fun t => t ◇ (a ◇ a)) (pw a))).symm).trans (pr a)
  have p1j:=fun (a:G)=>by
    exact ((pw (((a ◇ a) ◇ a) ◇ (a ◇ a))).symm).trans (pt a)
  have p1k:=fun (a:G)=>by
    exact (((cg (fun t => a ◇ t) (pt a)).symm).trans (((cg (fun t => t ◇ (((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a)))) (p1j a)).symm).trans (p13 (((a ◇ a) ◇ a) ◇ (a ◇ a))))).symm
  have p1l:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))) (p1k a)).symm).trans (pt a)
  have p1m:=fun (a:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ a) (p1g a))).symm).trans (((cg (fun t => t ◇ ((a ◇ ((a ◇ a) ◇ a)) ◇ a)) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => t ◇ a) (p1g a)))).symm).trans (p0 ((a ◇ a) ◇ a) a))
  have p1n:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p1g a))).symm).trans (((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p1m a)))).symm).trans (pi a (a ◇ a)))
  have p1o:=fun (a:G)=>by
    exact ((((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p1n a)).symm).trans (pw ((a ◇ a) ◇ a))).trans (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p1n a))).symm
  have p1p:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p1g a))).symm).trans (pv a)
  have p1q:=fun (a b:G)=>by
    exact (((((((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (cg (fun t => t ◇ (a ◇ a)) (p17 a))))))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p17 a))))))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => (a ◇ a) ◇ t) (p17 a))))))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a))) (cg (fun t => t ◇ b) (p17 a)))))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p17 a)))))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p17 a))))).symm).trans (((cg (fun t => t ◇ (b ◇ ((((((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ b) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a))))) (p16 a)).symm).trans (pi (a ◇ a) b))
  have p1r:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ a) (p1c b))))).symm).trans (p9 (b ◇ b) b a b)
  have p1s:=fun (a:G)=>by
    exact (((((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a)))) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (p1k a)))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a)))) (p1m a)))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => a ◇ t) (p1k a)))).symm).trans (((cg (fun t => t ◇ (((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a)))) ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))))) (p1k a)).symm).trans (p1c (((a ◇ a) ◇ a) ◇ (a ◇ a))))).symm
  have p1t:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p1f b)))).symm).trans ((h a (b ◇ (b ◇ b)) b).symm)
  have p1u:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p1h b)))).symm).trans ((h a ((b ◇ b) ◇ b) b).symm)
  have p1v:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => ((b ◇ (b ◇ b)) ◇ a) ◇ t) (p18 b)))).symm).trans ((h a b (b ◇ (b ◇ b))).symm)
  have p1w:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ (a ◇ a)))) (p1f a)))).symm).trans ((h a b (a ◇ (a ◇ a))).symm)
  have p1x:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))) (p1m a)).symm).trans (((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (p1k a))).symm).trans (p1f (((a ◇ a) ◇ a) ◇ (a ◇ a))))
  have p1y:=fun (a b:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (a ◇ b)) (p18 b)))).symm).trans ((h (b ◇ (b ◇ b)) a b).symm)
  have p1z:=fun (a b:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => t ◇ (a ◇ b)) (p1g b)))).symm).trans ((h ((b ◇ b) ◇ b) a b).symm)
  have p20:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ ((b ◇ a) ◇ b)) ◇ (a ◇ b))) (p1g b)).symm).trans (((cg (fun t => (b ◇ ((b ◇ b) ◇ b)) ◇ t) (cg (fun t => (a ◇ ((b ◇ a) ◇ b)) ◇ t) (cg (fun t => t ◇ b) (p1u a b)))).symm).trans (pd b b (a ◇ ((b ◇ a) ◇ b))))
  have p21:=fun (a b:G)=>by
    exact (((((cg (fun t => b ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pc a))))))).trans (cg (fun t => b ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (p1n a))))))).trans (cg (fun t => b ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => b ◇ t) (p1m a)))))).trans (cg (fun t => b ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (b ◇ a))) (p1n a)))).symm).trans ((((cg (fun t => b ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (b ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ ((((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a)))))) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pc a)))).symm).trans (pb (((a ◇ a) ◇ a) ◇ (a ◇ a)) ((a ◇ a) ◇ a) b)).trans ((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pc a)).trans (p1n a)))
  have p22:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => ((b ◇ a) ◇ b) ◇ t) (cg (fun t => b ◇ t) (p1t a b)))).symm).trans (pb a b (b ◇ (b ◇ b)))
  have p23:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p1r a b))).symm).trans ((((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ ((b ◇ a) ◇ (b ◇ b))))) (cg (fun t => t ◇ b) (p1r a b)))).symm).trans (p22 (a ◇ ((b ◇ a) ◇ (b ◇ b))) b)).trans (cg (fun t => t ◇ b) (p1r a b)))
  have p24:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ ((b ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (b ◇ ((a ◇ b) ◇ ((a ◇ a) ◇ a)))))) (cg (fun t => (a ◇ a) ◇ t) (p17 a))).trans (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (po a b)))).trans (cg (fun t => t ◇ ((b ◇ (a ◇ a)) ◇ b)) (p17 a))).symm).trans ((((cg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ (b ◇ ((a ◇ b) ◇ ((a ◇ a) ◇ a))))) (cg (fun t => t ◇ (a ◇ a)) (po a b)))).symm).trans (p22 (b ◇ ((a ◇ b) ◇ ((a ◇ a) ◇ a))) (a ◇ a))).trans (cg (fun t => t ◇ (a ◇ a)) (po a b)))
  have p25:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p24 a b)).symm).trans (p1t (a ◇ a) b)
  have p26:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p24 a b)).symm).trans (p1u (a ◇ a) b)
  have p27:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ b) ◇ t) (p24 a (b ◇ b))).symm).trans (p1q b (a ◇ a))
  have p28:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ (a ◇ a)) ◇ b)) (p24 a b)).symm).trans (p0 (a ◇ a) b)
  have p29:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p28 a b))).symm).trans ((h (a ◇ a) (b ◇ (a ◇ a)) b).symm)
  have p2a:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => ((a ◇ b) ◇ a) ◇ t) (cg (fun t => t ◇ b) (p23 a b)))).symm).trans (p1v ((a ◇ b) ◇ a) b)
  have p2b:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => ((b ◇ a) ◇ b) ◇ t) (cg (fun t => b ◇ t) (p1u a b)))).symm).trans (pb a b ((b ◇ b) ◇ b))
  have p2c:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p1r a b))).symm).trans ((((cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ ((b ◇ a) ◇ (b ◇ b))))) (cg (fun t => t ◇ b) (p1r a b)))).symm).trans (p2b (a ◇ ((b ◇ a) ◇ (b ◇ b))) b)).trans (cg (fun t => t ◇ b) (p1r a b)))
  have p2d:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (b ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (p1g b))).symm).trans (p4 b a (b ◇ b) b)
  have p2e:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => (b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ a))) ◇ t) (p18 b))).symm).trans (p4 b a b (b ◇ b))
  have p2f:=fun (a b:G)=>by
    exact ((p1f ((b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ a))) ◇ b)).symm).trans ((((cg (fun t => (((b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ a))) ◇ b) ◇ (((b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ a))) ◇ b) ◇ ((b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ a))) ◇ b))) ◇ t) (cg (fun t => t ◇ b) (p2e a b))).symm).trans (p23 b ((b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ a))) ◇ b))).trans (p2e a b))
  have p2g:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ (b ◇ b))) (p1m a)).symm).trans (((cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ (b ◇ b))) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (p1k a))).symm).trans (p25 b (((a ◇ a) ◇ a) ◇ (a ◇ a))))
  have p2h:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (p2f a b)).symm).trans (p2e a b)
  have p2i:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a))) ◇ b) ◇ t) (p18 b)).symm).trans (((cg (fun t => t ◇ (b ◇ (b ◇ (b ◇ b)))) (cg (fun t => (b ◇ ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a))) ◇ t) (p18 b))).symm).trans (pf a (b ◇ (b ◇ b)) b))
  have p2j:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ b) ◇ t) (p1g b)).symm).trans (((cg (fun t => t ◇ (b ◇ ((b ◇ b) ◇ b))) (cg (fun t => (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ t) (p1g b))).symm).trans (pf a ((b ◇ b) ◇ b) b))
  have p2k:=fun (a b:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => t ◇ (b ◇ b)) (p1s a))).symm).trans (p2g a b)
  have p2l:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ a)) (cg (fun t => t ◇ (b ◇ a)) (cg (fun t => b ◇ t) (cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (p18 a))))).symm).trans (pf (a ◇ (a ◇ a)) a b)
  have p2m:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => t ◇ a) (cg (fun t => t ◇ c) (cg (fun t => a ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p1f b))))))).symm).trans (p9 a b c (b ◇ (b ◇ b)))
  have p2n:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))) ◇ b)) (p1m a)).symm).trans (((cg (fun t => t ◇ ((b ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))) ◇ b)) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (p1k a))).symm).trans (p23 b (((a ◇ a) ◇ a) ◇ (a ◇ a))))
  have p2o:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ b)) (p1a a)).symm).trans (((cg (fun t => t ◇ ((b ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ b)) (cg (fun t => ((a ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (p1b a))).symm).trans (p23 b ((a ◇ (a ◇ a)) ◇ (a ◇ a))))
  have p2p:=fun (a:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (pw a))).symm).trans (p1k a)
  have p2q:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (cg (fun t => b ◇ t) (cg (fun t => (((a ◇ b) ◇ a) ◇ b) ◇ t) (p23 a b))))).symm).trans (p2i ((a ◇ b) ◇ a) b)
  have p2r:=fun (a b:G)=>by
    exact (((p2o a b).symm).trans (((cg (fun t => a ◇ t) (cg (fun t => t ◇ b) (cg (fun t => b ◇ t) (cg (fun t => t ◇ (a ◇ a)) (pw a))))).symm).trans (p2n a b))).symm
  have p2s:=fun (a b:G)=>by
    exact (((cg (fun t => b ◇ t) (p1o a)).symm).trans (p2r a b)).symm
  have p2t:=fun (a b:G)=>by
    exact (((((cg (fun t => b ◇ t) (cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a)))) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (p2p a)))).trans (cg (fun t => b ◇ t) (cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a)))) (p1m a)))).trans (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (p1k a)))).symm).trans ((((cg (fun t => b ◇ t) (cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a)))) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (p2r a (((a ◇ a) ◇ a) ◇ (a ◇ a)))))).symm).trans (p2s (((a ◇ a) ◇ a) ◇ (a ◇ a)) b)).trans (((cg (fun t => b ◇ t) (cg (fun t => ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))) (p1k a)))).trans (cg (fun t => b ◇ t) (cg (fun t => ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))) ◇ t) (p1l a)))).trans (cg (fun t => b ◇ t) (cg (fun t => t ◇ a) (p1k a)))))).symm
  have p2u:=fun (a b:G)=>by
    exact (((cg (fun t => b ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1n a))).symm).trans ((((cg (fun t => b ◇ t) (p2t a (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)))).symm).trans (p2t ((a ◇ a) ◇ a) b)).trans (cg (fun t => b ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p1n a))))).symm
  have p2v:=fun (a b:G)=>by
    exact (((cg (fun t => ((b ◇ ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a))) ◇ b) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p1p b))).trans (cg (fun t => ((b ◇ ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a))) ◇ b) ◇ t) (p17 b))).symm).trans (((cg (fun t => ((b ◇ ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a))) ◇ b) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p2i a b)))).symm).trans (p21 b ((b ◇ ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a))) ◇ b)))
  have p2w:=fun (a b:G)=>by
    exact (((cg (fun t => ((b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ b) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p1n b))).trans (cg (fun t => ((b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ b) ◇ t) (p17 b))).symm).trans (((cg (fun t => ((b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ b) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p2j a b)))).symm).trans (p21 b ((b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ b)))
  have p2x:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => (((a ◇ b) ◇ a) ◇ c) ◇ t) (p23 a b)))).symm).trans ((h c (b ◇ (b ◇ b)) ((a ◇ b) ◇ a)).symm)
  have p2y:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (c ◇ ((((b ◇ (a ◇ a)) ◇ b) ◇ c) ◇ b))) (p24 a b)).symm).trans (pd (a ◇ a) b c)
  have p2z:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => ((a ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ a))) (p1c a)))).symm).trans ((h ((a ◇ (a ◇ a)) ◇ (a ◇ a)) b (a ◇ a)).symm)
  have p30:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => ((a ◇ a) ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ a))) (p1d a)))).symm).trans ((h ((a ◇ a) ◇ (a ◇ (a ◇ a))) b (a ◇ a)).symm)
  have p31:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => (a ◇ ((b ◇ a) ◇ b)) ◇ t) (cg (fun t => a ◇ t) (p15 b)))).symm).trans (((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => (a ◇ ((b ◇ a) ◇ b)) ◇ t) (cg (fun t => t ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ b)))) (p1t a b)))).symm).trans (p1r (a ◇ ((b ◇ a) ◇ b)) (b ◇ (b ◇ b))))
  have p32:=fun (a b:G)=>by
    exact (((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p25 a (b ◇ (a ◇ a)))).symm).trans (((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => ((b ◇ (a ◇ a)) ◇ ((b ◇ (a ◇ a)) ◇ (b ◇ (a ◇ a)))) ◇ t) (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (p25 a b)))).symm).trans (p1y (b ◇ (b ◇ b)) (b ◇ (a ◇ a))))).symm
  have p33:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ a)) ◇ t) (p32 a b)).symm).trans (p18 (b ◇ (a ◇ a)))
  have p34:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (a ◇ a))) (p32 a b)).symm).trans (p1f (b ◇ (a ◇ a)))
  have p35:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (p17 a))).symm).trans (((cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (a ◇ a) ◇ t) (p17 a)))).symm).trans (p33 b (a ◇ a)))
  have p36:=fun (a b c:G)=>by
    exact (((cg (fun t => (c ◇ (c ◇ c)) ◇ t) (cg (fun t => c ◇ t) (p35 a b))).symm).trans (p25 ((a ◇ a) ◇ (b ◇ b)) c)).trans (p35 a b)
  have p37:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ a)) (cg (fun t => ((b ◇ b) ◇ (a ◇ a)) ◇ t) (p35 b a))).trans (cg (fun t => t ◇ (a ◇ a)) (p35 b a))).symm).trans (((cg (fun t => (((b ◇ b) ◇ (a ◇ a)) ◇ (((b ◇ b) ◇ (a ◇ a)) ◇ ((b ◇ b) ◇ (a ◇ a)))) ◇ t) (p29 a (b ◇ b))).symm).trans (p36 a b ((b ◇ b) ◇ (a ◇ a))))
  have p38:=fun (a b:G)=>by
    exact (((cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p26 a (b ◇ (a ◇ a)))).symm).trans (((cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => (((b ◇ (a ◇ a)) ◇ (b ◇ (a ◇ a))) ◇ (b ◇ (a ◇ a))) ◇ t) (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (p26 a b)))).symm).trans (p1z ((b ◇ b) ◇ b) (b ◇ (a ◇ a))))).symm
  have p39:=fun (a b:G)=>by
    exact (((p38 a b).symm).trans (pw (b ◇ (a ◇ a)))).trans (p32 a b)
  have p3a:=fun (a b c:G)=>by
    exact (((cg (fun t => ((c ◇ c) ◇ c) ◇ t) (p35 a b)).symm).trans (p39 ((a ◇ a) ◇ (b ◇ b)) c)).trans (cg (fun t => (c ◇ (c ◇ c)) ◇ t) (p35 a b))
  have p3b:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1n a))).symm).trans ((((cg (fun t => t ◇ (b ◇ b)) (p2t a (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)))).symm).trans (p39 b ((a ◇ a) ◇ a))).trans (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p1n a))))).symm
  have p3c:=fun (a b c:G)=>by
    exact (((cg (fun t => b ◇ t) (cg (fun t => t ◇ (a ◇ (b ◇ c))) (cg (fun t => a ◇ t) (cg (fun t => ((c ◇ (c ◇ c)) ◇ a) ◇ t) (p18 c))))).symm).trans (p4 a (c ◇ (c ◇ c)) b c)).trans (cg (fun t => a ◇ t) (cg (fun t => ((c ◇ (c ◇ c)) ◇ a) ◇ t) (p18 c)))
  have p3d:=fun (a b c:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => t ◇ ((c ◇ (a ◇ a)) ◇ (b ◇ c))) (p29 a c))).symm).trans ((((cg (fun t => b ◇ t) (cg (fun t => t ◇ ((c ◇ (a ◇ a)) ◇ (b ◇ c))) (cg (fun t => (c ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ c) (p25 a c))))).symm).trans (p3c (c ◇ (a ◇ a)) b c)).trans ((cg (fun t => (c ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ c) (p25 a c))).trans (p29 a c)))
  have p3e:=fun (a b c:G)=>by
    exact ((cg (fun t => c ◇ t) (p24 b (c ◇ ((a ◇ c) ◇ ((c ◇ c) ◇ a))))).symm).trans (((cg (fun t => c ◇ t) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => ((c ◇ ((a ◇ c) ◇ ((c ◇ c) ◇ a))) ◇ (b ◇ b)) ◇ t) (p2h a c)))).symm).trans (p3d b c (c ◇ ((a ◇ c) ◇ ((c ◇ c) ◇ a)))))
  have p3f:=fun (a b:G)=>by
    exact (((cg (fun t => (b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ a))) ◇ t) (p1a b)).trans (p2f a b)).symm).trans (((cg (fun t => (b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ a))) ◇ t) (cg (fun t => ((b ◇ (b ◇ b)) ◇ (b ◇ b)) ◇ t) (p3e a b b))).symm).trans (p2z b (b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ a)))))
  have p3g:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => ((a ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ t) (p1a b))).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => ((a ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (p3f a b)))).symm).trans (p1r ((a ◇ b) ◇ ((b ◇ b) ◇ a)) b))
  have p3h:=fun (a b:G)=>by
    exact ((p1f (((a ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ b)).symm).trans ((((cg (fun t => ((((a ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ b) ◇ ((((a ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ b) ◇ (((a ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ b))) ◇ t) (cg (fun t => t ◇ b) (p3g a b))).symm).trans (p23 b (((a ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ b))).trans (p3g a b))
  have p3i:=fun (a b:G)=>by
    exact ((p3f a b).symm).trans (((cg (fun t => b ◇ t) (p3h a b)).symm).trans (p3g a b))
  have p3j:=fun (a b:G)=>by
    exact ((p3h a b).symm).trans ((((cg (fun t => t ◇ b) (p3i a b)).symm).trans (p1i b)).trans (p1x b))
  have p3k:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => b ◇ t) (p4 b a b b))).symm).trans (p1w b (b ◇ ((a ◇ b) ◇ (b ◇ a))))
  have p3l:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) ((h b b a).symm)).symm).trans (p3k a b)
  have p3m:=fun (a b:G)=>by
    exact (((cg (fun t => (b ◇ b) ◇ t) (p3l a b)).symm).trans (p2d a b)).symm
  have p3n:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (p1n b))).symm).trans (((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p3m a b)))).symm).trans (po b ((a ◇ b) ◇ (b ◇ a))))
  have p3o:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ b))) (p32 b ((a ◇ b) ◇ (b ◇ a)))).trans (p34 b ((a ◇ b) ◇ (b ◇ a)))).symm).trans ((((cg (fun t => ((((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ b)) ◇ ((((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ b)) ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ b)))) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (p3n a b))).symm).trans (p23 (b ◇ b) (((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ b)))).trans (p3n a b))
  have p3p:=fun (a b:G)=>by
    exact ((p1f ((a ◇ b) ◇ (b ◇ a))).symm).trans (((cg (fun t => (((a ◇ b) ◇ (b ◇ a)) ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((a ◇ b) ◇ (b ◇ a)))) ◇ t) (p3o a b)).symm).trans (p25 b ((a ◇ b) ◇ (b ◇ a))))
  have p3q:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ b) ◇ t) (p3p b a)).symm).trans (((cg (fun t => t ◇ ((b ◇ a) ◇ (a ◇ b))) (p3p a b)).symm).trans (p3p (a ◇ b) (b ◇ a)))
  have p3r:=fun (a b:G)=>by
    exact (((cg (fun t => (b ◇ b) ◇ t) (p3q a b)).trans (p3q (b ◇ a) b)).symm).trans (p27 a b)
  have p3s:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ (b ◇ a))) (p3r a b)).symm).trans (pw (b ◇ (b ◇ a)))).trans (cg (fun t => (b ◇ (b ◇ a)) ◇ t) (p3r a b))).symm
  have p3t:=fun (a b:G)=>by
    exact (((cg (fun t => (a ◇ b) ◇ t) (p25 b (b ◇ a))).symm).trans (((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => ((b ◇ a) ◇ ((b ◇ a) ◇ (b ◇ a))) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p3p a b)))).symm).trans (p1y (a ◇ b) (b ◇ a)))).symm
  have p3u:=fun (a b:G)=>by
    exact (((p3t (a ◇ a) b).symm).trans (p32 a b)).symm
  have p3v:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ a) ◇ t) (p3t a b)).symm).trans (p18 (b ◇ a))
  have p3w:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ a)) (p3t a b)).symm).trans (p1f (b ◇ a))
  have p3x:=fun (a b:G)=>by
    exact (p39 a b).trans (p3u a b)
  have p3y:=fun (a b:G)=>by
    exact (((cg (fun t => (a ◇ b) ◇ t) (p26 b (b ◇ a))).symm).trans (((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => (((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ a)) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p3p a b)))).symm).trans (p1z (a ◇ b) (b ◇ a)))).symm
  have p3z:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ b)) (p17 a)).symm).trans (p3q b (a ◇ a))).symm
  have p40:=fun (a b:G)=>by
    exact (((p3q a b).symm).trans (((cg (fun t => (b ◇ b) ◇ t) (p17 a)).symm).trans (p3q (a ◇ a) b))).symm
  have p41:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ a)) (p3q a b)).symm).trans (p37 a b)
  have p42:=fun (a b:G)=>by
    exact (((cg (fun t => ((a ◇ b) ◇ (b ◇ b)) ◇ t) (p3t a b)).trans (p40 b (a ◇ b))).symm).trans ((((cg (fun t => t ◇ ((b ◇ a) ◇ ((b ◇ a) ◇ (b ◇ a)))) (p3t a b)).symm).trans (p40 (b ◇ a) (b ◇ a))).trans (p17 (b ◇ a)))
  have p43:=fun (a b c:G)=>by
    exact ((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => ((b ◇ a) ◇ c) ◇ t) (p3p a b)))).symm).trans ((h c (a ◇ b) (b ◇ a)).symm)
  have p44:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p2t a b)).symm).trans (p3p ((a ◇ a) ◇ a) b)
  have p45:=fun (a b c:G)=>by
    exact ((cg (fun t => c ◇ t) (cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ (c ◇ (a ◇ b))) (p3p a b)))).symm).trans ((h (b ◇ a) c (a ◇ b)).symm)
  have p46:=fun (a b:G)=>by
    exact (((cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ b) (cg (fun t => t ◇ (a ◇ a)) (p17 a)))))).trans (cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ b) (p17 a)))))).symm).trans ((((cg (fun t => b ◇ t) (cg (fun t => ((a ◇ a) ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ b)) ◇ t) (p2y a (a ◇ a) b))).symm).trans (p45 ((((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ b) (a ◇ a) b)).trans ((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ b) (cg (fun t => t ◇ (a ◇ a)) (p17 a)))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ b) (p17 a)))))
  have p47:=fun (a b:G)=>by
    exact (((cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (p3q a b)).symm).trans (p3p (a ◇ a) (b ◇ b))).trans (p17 b)
  have p48:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (p3p b a)))).symm).trans (p43 a b (a ◇ b))
  have p49:=fun (a b:G)=>by
    exact ((((cg (fun t => (a ◇ b) ◇ t) (p3z a (b ◇ b))).trans (cg (fun t => (a ◇ b) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p17 b)))).symm).trans ((((cg (fun t => t ◇ (((a ◇ a) ◇ (b ◇ b)) ◇ ((a ◇ a) ◇ (b ◇ b)))) (p48 a b)).symm).trans (p3s ((a ◇ a) ◇ (b ◇ b)) (a ◇ b))).trans (((cg (fun t => t ◇ ((a ◇ b) ◇ ((a ◇ b) ◇ ((a ◇ a) ◇ (b ◇ b))))) (p3z a (b ◇ b))).trans (cg (fun t => t ◇ ((a ◇ b) ◇ ((a ◇ b) ◇ ((a ◇ a) ◇ (b ◇ b))))) (cg (fun t => (a ◇ a) ◇ t) (p17 b)))).trans (cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (p48 a b))))).symm
  have p4a:=fun (a b:G)=>by
    exact (((p3y b a).symm).trans (((cg (fun t => t ◇ (a ◇ b)) (p3q b a)).symm).trans (p49 a b))).symm
  have p4b:=fun (a b:G)=>by
    exact (((((cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (cg (fun t => ((a ◇ b) ◇ ((a ◇ b) ◇ (a ◇ b))) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p4a a b)))).trans (cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ ((a ◇ b) ◇ ((b ◇ a) ◇ (a ◇ a)))) (p3t b a)))).trans (cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (cg (fun t => ((b ◇ a) ◇ (a ◇ a)) ◇ t) (p3v b a)))).trans (cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (p3w b a))).symm).trans ((((cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (cg (fun t => ((a ◇ b) ◇ ((a ◇ b) ◇ (a ◇ b))) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p49 a b)))).symm).trans (p1y ((a ◇ a) ◇ (b ◇ b)) (a ◇ b))).trans (p3t b a))
  have p4c:=fun (a b:G)=>by
    exact ((((cg (fun t => ((((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b) ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b)) ◇ t) (cg (fun t => t ◇ b) (p46 a b))).trans (p3y b ((a ◇ a) ◇ ((a ◇ a) ◇ b)))).trans (cg (fun t => (b ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ b))) ◇ t) (p3r b (a ◇ a)))).symm).trans (((cg (fun t => t ◇ ((b ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b)) ◇ b)) (cg (fun t => (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b) ◇ t) (cg (fun t => t ◇ b) (p46 a b)))).symm).trans (p0 (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b) b))
  have p4d:=fun (a b c:G)=>by
    exact (((cg (fun t => ((c ◇ c) ◇ c) ◇ t) (p3q b a)).symm).trans (p3a a b c)).symm
  have p4e:=fun (a b c:G)=>by
    exact (((((cg (fun t => t ◇ ((b ◇ b) ◇ (c ◇ c))) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (p44 a (a ◇ a)))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ (c ◇ c))) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (p17 a)))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ (c ◇ c))) (p1m a))).symm).trans ((((cg (fun t => t ◇ ((b ◇ b) ◇ (c ◇ c))) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (p2u a (((a ◇ a) ◇ a) ◇ (a ◇ a))))).symm).trans (p4d b c (((a ◇ a) ◇ a) ◇ (a ◇ a)))).trans ((cg (fun t => t ◇ ((b ◇ c) ◇ (b ◇ c))) (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))) (p1k a))).trans (cg (fun t => t ◇ ((b ◇ c) ◇ (b ◇ c))) (p1l a))))).symm
  have p4f:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ b) ◇ (c ◇ c))) (p17 a)).symm).trans ((((cg (fun t => t ◇ ((b ◇ b) ◇ (c ◇ c))) (cg (fun t => (a ◇ a) ◇ t) (p17 a))).symm).trans (p4d b c (a ◇ a))).trans (((cg (fun t => t ◇ ((b ◇ c) ◇ (b ◇ c))) (cg (fun t => t ◇ (a ◇ a)) (p17 a))).trans (cg (fun t => t ◇ ((b ◇ c) ◇ (b ◇ c))) (p17 a))).trans (p3q (b ◇ c) a)))
  have p4g:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ (c ◇ c)) (cg (fun t => ((a ◇ b) ◇ (a ◇ b)) ◇ t) (p4e ((a ◇ b) ◇ (a ◇ b)) a b))).symm).trans (p3u c ((a ◇ b) ◇ (a ◇ b)))).trans ((((cg (fun t => t ◇ (((a ◇ b) ◇ (a ◇ b)) ◇ ((a ◇ b) ◇ (a ◇ b)))) (p3q (a ◇ b) c)).trans (cg (fun t => ((c ◇ (a ◇ b)) ◇ (c ◇ (a ◇ b))) ◇ t) (p17 (a ◇ b)))).trans (p3q (a ◇ b) (c ◇ (a ◇ b)))).trans (p42 c (a ◇ b)))
  have p4h:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ (c ◇ c)) (cg (fun t => t ◇ (((a ◇ b) ◇ (a ◇ b)) ◇ ((a ◇ a) ◇ (b ◇ b)))) (cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ b))) (p17 (a ◇ b))))).trans (cg (fun t => t ◇ (c ◇ c)) (cg (fun t => t ◇ (((a ◇ b) ◇ (a ◇ b)) ◇ ((a ◇ a) ◇ (b ◇ b)))) (p17 (a ◇ b))))).trans (p4g a b c)).symm).trans ((((cg (fun t => t ◇ (c ◇ c)) (cg (fun t => ((((a ◇ b) ◇ (a ◇ b)) ◇ ((a ◇ b) ◇ (a ◇ b))) ◇ ((a ◇ b) ◇ (a ◇ b))) ◇ t) (p4e ((a ◇ b) ◇ (a ◇ b)) a b))).symm).trans (p3b ((a ◇ b) ◇ (a ◇ b)) c)).trans ((((cg (fun t => t ◇ (c ◇ c)) (cg (fun t => (((a ◇ b) ◇ (a ◇ b)) ◇ ((a ◇ b) ◇ (a ◇ b))) ◇ t) (cg (fun t => ((a ◇ b) ◇ (a ◇ b)) ◇ t) (p17 (a ◇ b))))).trans (cg (fun t => t ◇ (c ◇ c)) (cg (fun t => t ◇ (((a ◇ b) ◇ (a ◇ b)) ◇ ((a ◇ b) ◇ (a ◇ b)))) (p17 (a ◇ b))))).trans (cg (fun t => t ◇ (c ◇ c)) (cg (fun t => ((a ◇ b) ◇ (a ◇ b)) ◇ t) (p17 (a ◇ b))))).trans (cg (fun t => t ◇ (c ◇ c)) (p17 (a ◇ b)))))
  have p4i:=fun (a b c:G)=>by
    exact (((((((cg (fun t => t ◇ (c ◇ c)) (cg (fun t => t ◇ (((a ◇ a) ◇ (b ◇ b)) ◇ (a ◇ b))) (p4b a b))).trans (cg (fun t => t ◇ (c ◇ c)) (cg (fun t => ((b ◇ a) ◇ (a ◇ a)) ◇ t) (p4b a b)))).trans (cg (fun t => t ◇ (c ◇ c)) (p40 a (b ◇ a)))).trans (cg (fun t => t ◇ (c ◇ c)) (p4h b a a))).trans (cg (fun t => t ◇ (c ◇ c)) (p41 a b))).symm).trans ((((cg (fun t => t ◇ (c ◇ c)) (p4f ((a ◇ a) ◇ (b ◇ b)) a b)).symm).trans (p3x c ((a ◇ a) ◇ (b ◇ b)))).trans (((((cg (fun t => t ◇ (((a ◇ a) ◇ (b ◇ b)) ◇ ((a ◇ a) ◇ (b ◇ b)))) (p4f c a b)).trans (cg (fun t => ((c ◇ (a ◇ b)) ◇ (c ◇ (a ◇ b))) ◇ t) (p40 b (a ◇ a)))).trans (cg (fun t => ((c ◇ (a ◇ b)) ◇ (c ◇ (a ◇ b))) ◇ t) (p4h a a b))).trans (cg (fun t => ((c ◇ (a ◇ b)) ◇ (c ◇ (a ◇ b))) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (p17 a)))).trans (p4f (c ◇ (a ◇ b)) a b)))).symm
  have p4j:=fun (a b c:G)=>by
    exact ((((((((cg (fun t => t ◇ ((c ◇ ((a ◇ b) ◇ (a ◇ b))) ◇ ((a ◇ b) ◇ (a ◇ b)))) (cg (fun t => t ◇ ((a ◇ a) ◇ (b ◇ b))) (p4e c a b))).trans (cg (fun t => ((c ◇ ((a ◇ a) ◇ (b ◇ b))) ◇ ((a ◇ a) ◇ (b ◇ b))) ◇ t) (cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ b))) (p4e c a b)))).trans (cg (fun t => ((c ◇ ((a ◇ a) ◇ (b ◇ b))) ◇ ((a ◇ a) ◇ (b ◇ b))) ◇ t) (p4e (c ◇ ((a ◇ a) ◇ (b ◇ b))) a b))).trans (p4i (a ◇ a) (b ◇ b) c)).trans (cg (fun t => t ◇ (c ◇ c)) (cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (p17 a)))).trans (cg (fun t => t ◇ (c ◇ c)) (cg (fun t => (a ◇ a) ◇ t) (p17 b)))).symm).trans ((((cg (fun t => t ◇ ((c ◇ ((a ◇ b) ◇ (a ◇ b))) ◇ ((a ◇ b) ◇ (a ◇ b)))) (p4e (c ◇ ((a ◇ b) ◇ (a ◇ b))) a b)).symm).trans (p4i (a ◇ b) (a ◇ b) c)).trans (cg (fun t => t ◇ (c ◇ c)) (p17 (a ◇ b))))).symm
  have p4k:=fun (a b c:G)=>by
    exact (p4h a b c).trans (p4j a b c)
  have p4l:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ b))) ◇ t) (p1e b)).symm).trans (((cg (fun t => (b ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ b))) ◇ t) (cg (fun t => ((b ◇ b) ◇ (b ◇ (b ◇ b))) ◇ t) (cg (fun t => b ◇ t) (p4c a b)))).symm).trans (p30 b (b ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ b)))))
  have p4m:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ b)) (p15 a)).symm).trans (p3q b (a ◇ (a ◇ a)))).symm
  have p4n:=fun (a b:G)=>by
    exact (((((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ ((a ◇ b) ◇ a))) (p2c a b))).trans (cg (fun t => (a ◇ b) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p2c a b)))).trans (p3t b a)).symm).trans ((((cg (fun t => t ◇ ((((b ◇ b) ◇ b) ◇ ((a ◇ b) ◇ a)) ◇ (((b ◇ b) ◇ b) ◇ ((a ◇ b) ◇ a)))) (p2c a b)).symm).trans (p3t ((a ◇ b) ◇ a) ((b ◇ b) ◇ b))).trans (cg (fun t => (((a ◇ b) ◇ a) ◇ ((b ◇ b) ◇ b)) ◇ t) (p1n b)))).symm
  have p4o:=fun (a b:G)=>by
    exact (((cg (fun t => (b ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ b))) ◇ t) (p2k b (b ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ b))))).trans (p3t ((a ◇ a) ◇ ((a ◇ a) ◇ b)) b)).symm).trans (((cg (fun t => (b ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ b))) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => t ◇ ((b ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ b))) ◇ (b ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ b))))) (p4l a b)))).symm).trans (p1r b (b ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ b)))))
  have p4p:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b))) (cg (fun t => (b ◇ b) ◇ t) (p17 b))).trans (cg (fun t => t ◇ (b ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b))) (p17 b))).trans (cg (fun t => (b ◇ b) ◇ t) (p46 a b))).symm).trans ((((cg (fun t => ((b ◇ b) ◇ ((b ◇ b) ◇ (b ◇ b))) ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b)) (p4o a b))).symm).trans (p23 (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ b) (b ◇ b))).trans (p4o a b))
  have p4q:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p3r b (a ◇ a))).trans (p3j b b)).symm).trans (((cg (fun t => (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ b))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p4p a b))).symm).trans (p4p b ((a ◇ a) ◇ ((a ◇ a) ◇ b))))).symm
  have p4r:=fun (a b:G)=>by
    exact ((((((cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ b))) (p4q a b))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ b)) ◇ t) (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ b)) ◇ t) (p4q a b)))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ b)) ◇ t) (p1k b))).trans (p1m b)).symm).trans ((((cg (fun t => t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ b)))) (p4q a b)).symm).trans (p3t ((a ◇ a) ◇ b) (a ◇ a))).trans (cg (fun t => (((a ◇ a) ◇ b) ◇ (a ◇ a)) ◇ t) (p17 a)))).symm
  have p4s:=fun (a b:G)=>by
    exact (((cg (fun t => ((b ◇ ((((a ◇ b) ◇ a) ◇ b) ◇ (a ◇ b))) ◇ b) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p1p b))).trans (cg (fun t => ((b ◇ ((((a ◇ b) ◇ a) ◇ b) ◇ (a ◇ b))) ◇ b) ◇ t) (p17 b))).symm).trans (((cg (fun t => ((b ◇ ((((a ◇ b) ◇ a) ◇ b) ◇ (a ◇ b))) ◇ b) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p2q a b)))).symm).trans (p21 b ((b ◇ ((((a ◇ b) ◇ a) ◇ b) ◇ (a ◇ b))) ◇ b)))
  have p4t:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (((b ◇ b) ◇ ((b ◇ ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a))) ◇ b)) ◇ (b ◇ b)) ◇ t) (p2v a b))))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (p4r b ((b ◇ ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a))) ◇ b)))))).trans (cg (fun t => (((b ◇ b) ◇ ((b ◇ ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a))) ◇ b)) ◇ (b ◇ b)) ◇ t) (p17 b))).trans (p4r b ((b ◇ ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a))) ◇ b))).symm).trans ((((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => t ◇ (((b ◇ ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a))) ◇ b) ◇ (b ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ ((b ◇ ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a))) ◇ b)) (p2v a b))))))).symm).trans (p4s ((b ◇ ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a))) ◇ b) (b ◇ b))).trans (p17 b))
  have p4u:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (((b ◇ b) ◇ ((b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ b)) ◇ (b ◇ b)) ◇ t) (p2w a b))))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (p4r b ((b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ b)))))).trans (cg (fun t => (((b ◇ b) ◇ ((b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ b)) ◇ (b ◇ b)) ◇ t) (p17 b))).trans (p4r b ((b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ b))).symm).trans ((((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => t ◇ (((b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ b) ◇ (b ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ ((b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ b)) (p2w a b))))))).symm).trans (p4s ((b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ b) (b ◇ b))).trans (p17 b))
  have p4v:=fun (a b:G)=>by
    exact ((((((((((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p40 b ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a)))).trans (p4e (b ◇ (b ◇ b)) ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a)) b)).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (p4k a b ((b ◇ (b ◇ b)) ◇ a))))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (p4m b a))))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (p3q a b))))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (p47 a b)))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p17 b))).trans (p3u b b)).symm).trans ((((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a)) ◇ (b ◇ b))) (cg (fun t => ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a)) ◇ t) (p4t a b)))).symm).trans (p31 ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a)) b)).trans (cg (fun t => ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a)) ◇ t) (p4t a b)))).symm
  have p4w:=fun (a b:G)=>by
    exact (((cg (fun t => ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a)) ◇ t) (cg (fun t => b ◇ t) (pc b))).trans (cg (fun t => ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a)) ◇ t) (p1g b))).symm).trans (((cg (fun t => ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a)) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p4v a b)))).symm).trans (pp b ((a ◇ b) ◇ ((b ◇ (b ◇ b)) ◇ a))))
  have p4x:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (cg (fun t => ((a ◇ ((b ◇ a) ◇ b)) ◇ b) ◇ t) (p1t a b))).symm).trans (p4w (a ◇ ((b ◇ a) ◇ b)) b)
  have p4y:=fun (a b:G)=>by
    exact (((p2m a b b).symm).trans (((cg (fun t => t ◇ (b ◇ (((a ◇ ((b ◇ a) ◇ b)) ◇ b) ◇ a))) (cg (fun t => t ◇ (b ◇ b)) (p4x a b))).symm).trans (p3w (((a ◇ ((b ◇ a) ◇ b)) ◇ b) ◇ a) b))).symm
  have p4z:=fun (a b:G)=>by
    exact ((((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (((a ◇ ((b ◇ a) ◇ b)) ◇ b) ◇ a) ◇ t) (p1g b))).trans (cg (fun t => (b ◇ b) ◇ t) (p4x a b))).symm).trans (((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (((a ◇ ((b ◇ a) ◇ b)) ◇ b) ◇ a) ◇ t) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p4y a b)))).symm).trans (po b (((a ◇ ((b ◇ a) ◇ b)) ◇ b) ◇ a)))).symm
  have p50:=fun (a b:G)=>by
    exact ((((((((((((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p40 b ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)))).trans (p4e (b ◇ (b ◇ b)) ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) b)).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (p4k a b (((b ◇ b) ◇ b) ◇ a))))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (p4k (b ◇ b) b a))))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (b ◇ b)) (p17 b))))))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p17 b)))))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (p3q a b))))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (p47 a b)))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p17 b))).trans (p3u b b)).symm).trans ((((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ (b ◇ b))) (cg (fun t => ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ t) (p4u a b)))).symm).trans (p31 ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) b)).trans (cg (fun t => ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ t) (p4u a b)))).symm
  have p51:=fun (a b:G)=>by
    exact (((cg (fun t => ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ t) (cg (fun t => b ◇ t) (pc b))).trans (cg (fun t => ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ t) (p1g b))).symm).trans (((cg (fun t => ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p50 a b)))).symm).trans (pp b ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))))
  have p52:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)))) (p51 a b)).symm).trans (p3p ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) b)
  have p53:=fun (a b:G)=>by
    exact (((((((((cg (fun t => t ◇ (b ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => b ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)))) (cg (fun t => t ◇ b) (p3t ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) b)))))).trans (cg (fun t => t ◇ (b ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => b ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ b)) (p51 a b)))))))).trans (cg (fun t => t ◇ (b ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => b ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)))) (p1f b)))))).trans (cg (fun t => t ◇ (b ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => b ◇ t) (p52 a b))))).trans (cg (fun t => t ◇ (b ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))))) (p3u b b))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ b)) ◇ t) (p52 a b))).trans (p1m b)).symm).trans (((cg (fun t => t ◇ (b ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))))) (cg (fun t => (b ◇ ((((b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ ((b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))))) ◇ b) ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))))) ◇ t) (p52 a b))).symm).trans (p2l (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) b))).symm
  have p54:=fun (a b:G)=>by
    exact ((((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p50 a b)).trans (p23 (b ◇ b) b)).symm).trans (((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ t) (cg (fun t => t ◇ b) (p53 a b)))).symm).trans (p1t ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) b))).symm
  have p55:=fun (a b:G)=>by
    exact (((((((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p4k (a ◇ a) a (a ◇ b))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ b))) (cg (fun t => t ◇ (a ◇ a)) (p17 a))))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ b))) (p17 a)))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p3q (a ◇ b) a))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p3r b a))).trans (p3u b b)).symm).trans (((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ b)) ◇ t) (cg (fun t => t ◇ (a ◇ b)) (p54 (a ◇ b) a)))).symm).trans (p2x a b (((a ◇ a) ◇ a) ◇ (a ◇ b))))
  have p56:=fun (a b c:G)=>by
    exact (((p55 a c).symm).trans (p55 b c)).symm
  have p57:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))) (p3j a a)).trans (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (p1n a))).trans (p1m a)).symm).trans (((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p1n a))).symm).trans (p55 b ((a ◇ a) ◇ a)))).symm
  have p58:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ ((a ◇ a) ◇ a)) ◇ b) ◇ t) (p57 a b)).symm).trans (p54 (b ◇ ((a ◇ a) ◇ a)) b)
  have p59:=fun (a b:G)=>by
    exact ((((((((cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ b)) ◇ t) (p4k (a ◇ a) a (a ◇ b))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ b))) (cg (fun t => t ◇ (a ◇ a)) (p17 a))))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ b))) (p17 a)))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ b)) ◇ t) (p3q (a ◇ b) a))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ b)) ◇ t) (p3r b a))).trans (p1m b)).symm).trans ((((cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ b)) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ b)))) ((p55 a b).symm)).symm).trans (p3t (a ◇ b) ((a ◇ a) ◇ a))).trans (cg (fun t => ((a ◇ b) ◇ ((a ◇ a) ◇ a)) ◇ t) (p1n a)))).symm
  have p5a:=fun (a b:G)=>by
    exact (((p4n a b).symm).trans (((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p2a a b))).symm).trans (p59 b (((a ◇ b) ◇ a) ◇ ((a ◇ b) ◇ b))))).symm
  have p5b:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (p5a a b)).symm).trans (p2a a b)
  have p5c:=fun (a b:G)=>by
    exact (((cg (fun t => (a ◇ b) ◇ t) (p3q (b ◇ a) b)).trans (cg (fun t => (a ◇ b) ◇ t) (p3r a b))).symm).trans ((((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => t ◇ ((b ◇ a) ◇ (b ◇ a))) (p3p a b))).symm).trans (p5b (b ◇ a) (a ◇ b))).trans (cg (fun t => t ◇ (b ◇ a)) (p3p b a)))
  have p5d:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ ((b ◇ b) ◇ b)) ◇ a) ◇ t) (p57 a b)).symm).trans (((cg (fun t => ((a ◇ ((b ◇ b) ◇ b)) ◇ a) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => b ◇ t) (p58 b a)))).symm).trans (p1z ((a ◇ ((b ◇ b) ◇ b)) ◇ a) b))
  have p5e:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (cg (fun t => b ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ (a ◇ a)))) (p1k a))))).trans (cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (cg (fun t => b ◇ t) (p1d a))))).symm).trans ((((cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (cg (fun t => b ◇ t) (p2u a ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))))))).symm).trans (p5d b (((a ◇ a) ◇ a) ◇ (a ◇ a)))).trans ((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))) (p1k a)).trans (p1l a)))
  have p5f:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ ((b ◇ a) ◇ b))) (p5e a b)).symm).trans (p3p ((b ◇ a) ◇ b) b)
  have p5g:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (p5f b a))).symm).trans (p5e (a ◇ ((a ◇ b) ◇ a)) b)
  have p5h:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) (cg (fun t => t ◇ c) ((h a c b).symm))).symm).trans (p5e (a ◇ ((b ◇ a) ◇ (c ◇ b))) c)).symm
  have p5i:=fun (a b c:G)=>by
    exact ((cg (fun t => b ◇ t) (p5h a (a ◇ a) b)).symm).trans (pp a b)
  have p5j:=fun (a b:G)=>by
    exact (((cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (p5e a b))).symm).trans (p5i ((b ◇ a) ◇ b) b a)).symm
  have p5k:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ b)) (p3p a b)).symm).trans (p5j (b ◇ a) (a ◇ b))).trans ((cg (fun t => (a ◇ b) ◇ t) (p3p b a)).trans (p5c a b))
  have p5l:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ c) (cg (fun t => t ◇ c) (p5h c a b))).symm).trans (p5e ((a ◇ c) ◇ (b ◇ a)) c)
  have p5m:=fun (a b c:G)=>by
    exact ((((p5l a b c).symm).trans (p5l b b c)).trans (p5c b c)).symm
  have p5n:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ b)) (p5k a b)).symm).trans (((cg (fun t => t ◇ (a ◇ b)) (cg (fun t => t ◇ (a ◇ b)) (p3p a b))).symm).trans (p5e (b ◇ a) (a ◇ b)))
  have p5o:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ ((a ◇ a) ◇ (b ◇ a))) (p5k (a ◇ a) (a ◇ b))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ (b ◇ a))) (cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ a))) (p17 a)))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ (b ◇ a))) (cg (fun t => (a ◇ a) ◇ t) (p5c a b)))).trans (p5g a ((a ◇ a) ◇ (b ◇ a)))).trans (cg (fun t => a ◇ t) (cg (fun t => t ◇ a) (p5h a a b)))).symm).trans (((cg (fun t => (((a ◇ b) ◇ (a ◇ b)) ◇ ((a ◇ a) ◇ (a ◇ b))) ◇ t) (p5c a b)).symm).trans (p5n (a ◇ b) (a ◇ a)))
  have p5p:=fun (a b:G)=>by
    exact (p5l a a b).trans (p5c a b)
  have p5q:=fun (a b c:G)=>by
    exact ((cg (fun t => b ◇ t) (p5m a b c)).symm).trans (p5h b b c)
  have p5r:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ b) (p5o b a)).symm).trans (p5j (((b ◇ a) ◇ a) ◇ b) b)).trans ((cg (fun t => b ◇ t) (p5p a b)).trans (p5q a b a))
  have p5s:=fun (a b c:G)=>by
    exact ((cg (fun t => b ◇ t) (p56 a c (b ◇ c))).symm).trans (p1z b c)
  have p5t:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ ((b ◇ a) ◇ b)) ◇ t) (p1u a b)).symm).trans ((((cg (fun t => (a ◇ ((b ◇ a) ◇ b)) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p20 a b))).symm).trans (p5s b (a ◇ ((b ◇ a) ◇ b)) (a ◇ b))).trans (p3y b a))
  have p5u:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (p5t b a)).symm).trans (p5e ((a ◇ b) ◇ a) b)
  have p5v:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ b)) (p5e a b))).symm).trans (p5u ((b ◇ a) ◇ b) b)).trans (cg (fun t => t ◇ ((b ◇ a) ◇ b)) (p5e a b))).symm
  have p5w:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ (((c ◇ c) ◇ c) ◇ (c ◇ ((a ◇ a) ◇ a)))) (cg (fun t => t ◇ a) (p5v b a))).trans (cg (fun t => (((b ◇ (a ◇ a)) ◇ a) ◇ a) ◇ t) (p57 a c))).symm).trans (((cg (fun t => ((b ◇ ((a ◇ b) ◇ a)) ◇ a) ◇ t) (cg (fun t => ((c ◇ c) ◇ c) ◇ t) (cg (fun t => c ◇ t) (p4z b a)))).symm).trans (p5s c ((b ◇ ((a ◇ b) ◇ a)) ◇ a) b))
  have p5x:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (p5w b a a)).symm).trans (p5i ((a ◇ (b ◇ b)) ◇ b) b a)
  have p5y:=fun (a b:G)=>by
    exact ((p5x a b).symm).trans (p2t a b)
  have p5z:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ b) (p5r a (b ◇ b))).symm).trans (p5y (((b ◇ b) ◇ (b ◇ b)) ◇ ((b ◇ b) ◇ a)) b)).trans ((((((((cg (fun t => b ◇ t) (cg (fun t => (((b ◇ b) ◇ (b ◇ b)) ◇ ((b ◇ b) ◇ a)) ◇ t) (cg (fun t => t ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ ((b ◇ b) ◇ a))) (cg (fun t => t ◇ ((b ◇ b) ◇ a)) (p17 b))))).trans (cg (fun t => b ◇ t) (cg (fun t => (((b ◇ b) ◇ (b ◇ b)) ◇ ((b ◇ b) ◇ a)) ◇ t) (cg (fun t => ((b ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ t) (cg (fun t => t ◇ ((b ◇ b) ◇ a)) (p17 b)))))).trans (cg (fun t => b ◇ t) (cg (fun t => t ◇ (((b ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ ((b ◇ b) ◇ ((b ◇ b) ◇ a)))) (cg (fun t => t ◇ ((b ◇ b) ◇ a)) (p17 b))))).trans (cg (fun t => b ◇ t) (cg (fun t => ((b ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ t) (cg (fun t => t ◇ ((b ◇ b) ◇ ((b ◇ b) ◇ a))) (p4q b a))))).trans (cg (fun t => b ◇ t) (cg (fun t => ((b ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (p4q b a))))).trans (cg (fun t => b ◇ t) (cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a)))) (p4q b a)))).trans (cg (fun t => b ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (p1k a)))).trans (cg (fun t => b ◇ t) (p1m a)))
  exact (calc
    (x ◇ y)=(x ◇ y):=rfl
    _=((((x ◇ x) ◇ y) ◇ y) ◇ x):=(p5z y x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6732_to_53146 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6732_to_53146
