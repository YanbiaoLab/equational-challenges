-- Equation56178 → Equation54898
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ z) = (y ◇ z) ◇ (x ◇ y)
-- Conclusion: x ◇ (y ◇ x) = x ◇ ((y ◇ x) ◇ y)
-- Original submission SHA-256: fa9ceee43e0c303fdb92e0730db62b4c7910a600510837debdd86aaf5f509c57
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = (y ◇ z) ◇ (x ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (y ◇ x) = x ◇ ((y ◇ x) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have p0:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ (d ◇ (b ◇ c))) ((h a b c).symm)).symm).trans ((h d (b ◇ c) (a ◇ b)).symm)
  have p1:=fun (a b c d:G)=>by
    exact ((cg (fun t => ((a ◇ b) ◇ d) ◇ t) ((h a b c).symm)).symm).trans ((h (b ◇ c) (a ◇ b) d).symm)
  have p2:=fun (a b:G)=>by
    exact ((p1 a a a b).symm).trans ((h a (a ◇ a) b).symm)
  have p3:=fun (a:G)=>by
    exact (((p2 a a).symm).trans ((h (a ◇ a) a a).symm)).symm
  have p4:=fun (a:G)=>by
    exact ((p3 a).symm).trans ((h a a a).symm)
  have p5:=fun (a:G)=>by
    exact (p3 a).trans (p4 a)
  have p6:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ b) ◇ t) ((h a b b).symm)).symm).trans (p2 b (a ◇ b))
  have p7:=fun (a b c:G)=>by
    exact ((p0 (a ◇ b) a b c).symm).trans ((h c (a ◇ b) (a ◇ b)).symm)
  have p8:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ b)) (p4 b)).symm).trans ((h a b ((b ◇ b) ◇ b)).symm)).trans (cg (fun t => a ◇ t) (p4 b))
  have p9:=fun (a b c d:G)=>by
    exact (((cg (fun t => (b ◇ (c ◇ d)) ◇ t) ((h c d a).symm)).symm).trans (p0 b c d (d ◇ a))).symm
  have pa:=fun (a b c d:G)=>by
    exact (((cg (fun t => (d ◇ a) ◇ t) ((h b c d).symm)).symm).trans (p9 a b c d)).symm
  have pb:=fun (a b c d e:G)=>by
    exact (((cg (fun t => t ◇ (e ◇ (a ◇ (b ◇ c)))) (p0 a b c d)).symm).trans ((h e (a ◇ (b ◇ c)) (d ◇ (b ◇ c))).symm)).trans (cg (fun t => e ◇ t) (p0 a b c d))
  have pc:=fun (a b c d:G)=>by
    exact (p9 a b c d).trans (pa a b c d)
  have pd:=fun (a b c:G)=>by
    exact ((pa a (b ◇ a) c b).symm).trans ((h c (b ◇ a) (c ◇ b)).symm)
  have pe:=fun (a b c:G)=>by
    exact (((cg (fun t => (b ◇ a) ◇ t) ((h c b a).symm)).symm).trans (pd a b c)).symm
  have pf:=fun (a b c:G)=>by
    exact (((cg (fun t => c ◇ t) ((h c b a).symm)).symm).trans (pe a b c)).symm
  have pg:=fun (a b c:G)=>by
    exact (pe a b c).trans (pf a b c)
  have ph:=fun (a b c:G)=>by
    exact (((pf b b a).symm).trans (p6 a b)).symm
  have pi:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) ((h a b b).symm)).symm).trans (ph a b a)
  have pj:=fun (a b c d e:G)=>by
    exact ((p1 d (b ◇ c) (a ◇ b) e).symm).trans (((cg (fun t => ((d ◇ (b ◇ c)) ◇ e) ◇ t) (p0 a b c d)).symm).trans ((h (a ◇ (b ◇ c)) (d ◇ (b ◇ c)) e).symm))
  have pk:=fun (a b c d:G)=>by
    exact (((cg (fun t => t ◇ (d ◇ (b ◇ c))) ((h b c a).symm)).symm).trans (p0 (c ◇ a) b c d)).symm
  have pl:=fun (a b c d:G)=>by
    exact (((cg (fun t => d ◇ t) ((h (c ◇ a) b c).symm)).symm).trans (pk a b c d)).symm
  have pm:=fun (a b c d:G)=>by
    exact (pk a b c d).trans (pl a b c d)
  have pn:=fun (a b c:G)=>by
    exact (((p1 c a b (a ◇ b)).symm).trans (p0 (c ◇ a) a b c)).symm
  have po:=fun (a b c:G)=>by
    exact (((cg (fun t => c ◇ t) ((h (c ◇ a) a b).symm)).symm).trans (pn a b c)).symm
  have pp:=fun (a b:G)=>by
    exact (((cg (fun t => (a ◇ b) ◇ t) ((h a b a).symm)).symm).trans (po a b b)).symm
  have pq:=fun (a b:G)=>by
    exact (((cg (fun t => b ◇ t) ((h a b a).symm)).symm).trans (pp a b)).symm
  have pr:=fun (a b c d e:G)=>by
    exact (((pb a b c d e).symm).trans (((cg (fun t => (d ◇ ((b ◇ c) ◇ (a ◇ b))) ◇ t) (cg (fun t => e ◇ t) ((h a b c).symm))).symm).trans (p0 d (b ◇ c) (a ◇ b) e))).symm
  have ps:=fun (a b c d:G)=>by
    exact (((cg (fun t => t ◇ (c ◇ (d ◇ b))) ((h c d a).symm)).symm).trans (pa b (d ◇ a) c d)).symm
  have pt:=fun (a b c d:G)=>by
    exact (((cg (fun t => (d ◇ b) ◇ t) ((h c d a).symm)).symm).trans (ps a b c d)).symm
  have pu:=fun (a b c d:G)=>by
    exact (ps a b c d).trans (pt a b c d)
  have pv:=fun (a b c:G)=>by
    exact (((cg (fun t => (c ◇ b) ◇ t) ((h c b a).symm)).symm).trans (pf b c (b ◇ a))).trans ((pu a a c b).trans (pf a b c))
  have pw:=fun (a b c:G)=>by
    exact (((pv a b a).symm).trans (pq a b)).symm
  have px:=fun (a:G)=>by
    exact (((((p1 a a a a).trans (p2 a a)).trans (p4 a)).symm).trans ((((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p4 a)).symm).trans (pf a (a ◇ a) a)).trans (cg (fun t => a ◇ t) (p4 a)))).symm
  have py:=fun (a b:G)=>by
    exact (((pf (a ◇ b) b a).symm).trans (pa (a ◇ b) b a b)).trans ((p0 b a b b).trans (pg b a b))
  have pz:=fun (a b:G)=>by
    exact ((cg (fun t => a ◇ t) (pw b a a)).symm).trans (py a b)
  have p10:=fun (a b c d e:G)=>by
    exact (((cg (fun t => ((d ◇ (b ◇ c)) ◇ e) ◇ t) (cg (fun t => d ◇ t) ((h a b c).symm))).symm).trans (p1 d (b ◇ c) (a ◇ b) e)).trans (pj a b c d e)
  have p11:=fun (a b c d:G)=>by
    exact ((p10 c a b c d).symm).trans ((h c (c ◇ (a ◇ b)) d).symm)
  have p12:=fun (a b c d:G)=>by
    exact (((cg (fun t => t ◇ (d ◇ ((b ◇ a) ◇ c))) ((h c b a).symm)).symm).trans (pl b (b ◇ a) c d)).trans (pm a c b d)
  have p13:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ c)) (pi a c)).symm).trans ((h b c (a ◇ (c ◇ c))).symm)).trans (cg (fun t => b ◇ t) (pi a c))
  have p14:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ c)) (pw a c a)).symm).trans ((h b c (a ◇ (c ◇ a))).symm)).trans (cg (fun t => b ◇ t) (pw a c (c ◇ (a ◇ (c ◇ a)))))
  have p15:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ a))) (p4 b)).symm).trans (pa a b (b ◇ b) b)).trans (cg (fun t => (b ◇ a) ◇ t) (p4 b))
  have p16:=fun (a b c d e:G)=>by
    exact (((p0 d a (b ◇ c) e).symm).trans (((cg (fun t => t ◇ (e ◇ (a ◇ (b ◇ c)))) (cg (fun t => d ◇ t) ((h a b c).symm))).symm).trans (pb a b c d e))).symm
  have p17:=fun (a b:G)=>by
    exact ((((p1 a a a b).trans (p2 a b)).symm).trans (((cg (fun t => ((a ◇ a) ◇ b) ◇ t) (px a)).symm).trans (p1 a a (a ◇ a) b))).symm
  have p18:=fun (a b:G)=>by
    exact (((p17 b (b ◇ a)).symm).trans (p15 a b)).symm
  have p19:=fun (a b:G)=>by
    exact ((((p0 a b b b).trans (ph a b (b ◇ ((b ◇ b) ◇ (a ◇ b))))).symm).trans ((((cg (fun t => (a ◇ (b ◇ b)) ◇ t) (px b)).symm).trans (pa (b ◇ b) a b b)).trans ((p0 b b b a).trans (cg (fun t => a ◇ t) (p5 b))))).symm
  have p1a:=fun (a b:G)=>by
    exact (p8 a b).trans (p19 a b)
  have p1b:=fun (a b:G)=>by
    exact ((((pl a b b b).trans (pg a b b)).symm).trans ((((cg (fun t => (b ◇ (b ◇ a)) ◇ t) (px b)).symm).trans (pt a (b ◇ b) b b)).trans (pa a b b b))).symm
  have p1c:=fun (a b:G)=>by
    exact (((p1b a b).symm).trans (p18 a b)).symm
  have p1d:=fun (a b c d:G)=>by
    exact (((cg (fun t => t ◇ (c ◇ d)) (pg a b d)).symm).trans ((h c d ((b ◇ a) ◇ (d ◇ b))).symm)).trans (cg (fun t => c ◇ t) (pg a b d))
  have p1e:=fun (a b c:G)=>by
    exact (((((cg (fun t => (b ◇ (a ◇ ((a ◇ a) ◇ a))) ◇ t) (cg (fun t => c ◇ t) (p5 a))).trans (cg (fun t => t ◇ (c ◇ (a ◇ (a ◇ a)))) (cg (fun t => b ◇ t) (p4 a)))).trans (p0 b a (a ◇ a) c)).trans (cg (fun t => c ◇ t) (p1a b a))).symm).trans ((((cg (fun t => t ◇ (c ◇ ((a ◇ a) ◇ (a ◇ a)))) (cg (fun t => b ◇ t) (p3 a))).symm).trans (p0 b (a ◇ a) (a ◇ a) c)).trans (((cg (fun t => c ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ a))) (p5 a))).trans (cg (fun t => c ◇ t) (p0 a a a b))).trans (cg (fun t => c ◇ t) (cg (fun t => b ◇ t) (p5 a)))))
  have p1f:=fun (a b c:G)=>by
    exact ((cg (fun t => ((a ◇ b) ◇ c) ◇ t) (p19 a b)).symm).trans (((cg (fun t => ((a ◇ b) ◇ c) ◇ t) (p8 a b)).symm).trans ((h (b ◇ (b ◇ b)) (a ◇ b) c).symm))
  have p1g:=fun (a b c d e:G)=>by
    exact (pr a b c d e).trans (p16 a b c d e)
  have p1h:=fun (a b c:G)=>by
    exact (((cg (fun t => (a ◇ (b ◇ (b ◇ b))) ◇ t) (cg (fun t => c ◇ t) (p4 b))).trans (cg (fun t => t ◇ (c ◇ (b ◇ (b ◇ b)))) (p19 a b))).symm).trans ((((cg (fun t => t ◇ (c ◇ (b ◇ ((b ◇ b) ◇ b)))) (cg (fun t => a ◇ t) (p4 b))).symm).trans (p0 a b ((b ◇ b) ◇ b) c)).trans ((cg (fun t => c ◇ t) (cg (fun t => t ◇ (a ◇ b)) (p4 b))).trans (cg (fun t => c ◇ t) (p1a a b))))
  have p1i:=fun (a b:G)=>by
    exact ((pf (a ◇ a) a b).symm).trans ((((cg (fun t => t ◇ (b ◇ (a ◇ (a ◇ a)))) (px a)).symm).trans (p1h a a b)).trans (cg (fun t => b ◇ t) (px a)))
  have p1j:=fun (a b:G)=>by
    exact (((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => b ◇ t) ((h a a a).symm))).symm).trans (pi b (a ◇ a))).trans ((cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p5 a))).trans (p1i a b))
  have p1k:=fun (a b c:G)=>by
    exact (((((cg (fun t => ((a ◇ (b ◇ b)) ◇ c) ◇ t) (ph a b (b ◇ ((b ◇ b) ◇ (a ◇ b))))).trans (p10 a b b a c)).trans (p11 b b a c)).symm).trans (((cg (fun t => ((a ◇ (b ◇ b)) ◇ c) ◇ t) (p6 a b)).symm).trans ((h (b ◇ b) (a ◇ (b ◇ b)) c).symm))).symm
  have p1l:=fun (a b:G)=>by
    exact (((cg (fun t => a ◇ t) (p0 a b b b)).trans (cg (fun t => a ◇ t) (ph a b (b ◇ ((b ◇ b) ◇ (a ◇ b)))))).symm).trans ((((p1k a b (b ◇ (b ◇ b))).symm).trans (p1j b (a ◇ (b ◇ b)))).trans ((p0 a b b b).trans (ph a b (b ◇ ((b ◇ b) ◇ (a ◇ b))))))
  have p1m:=fun (a b c d:G)=>by
    exact (((cg (fun t => t ◇ (d ◇ (b ◇ a))) (pf a b c)).symm).trans ((h d (b ◇ a) (c ◇ (b ◇ a))).symm)).trans (cg (fun t => d ◇ t) (pf a b c))
  have p1n:=fun (a b:G)=>by
    exact ((pv b (a ◇ a) a).symm).trans ((((cg (fun t => t ◇ (a ◇ ((a ◇ a) ◇ b))) (p4 a)).symm).trans (pt a b a (a ◇ a))).trans (((cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p4 a)).trans (p1 a a a b)).trans (p2 a b)))
  have p1o:=fun (a b c:G)=>by
    exact ((cg (fun t => ((a ◇ b) ◇ c) ◇ t) (pw b a a)).symm).trans (p1 a b (a ◇ b) c)
  have p1p:=fun (a b c:G)=>by
    exact (((cg (fun t => (a ◇ (b ◇ c)) ◇ t) (pw c b a)).symm).trans (pa (b ◇ c) a b c)).trans (p0 c b c a)
  have p1q:=fun (a b c:G)=>by
    exact (((p1m b a b c).symm).trans (((cg (fun t => t ◇ (c ◇ (a ◇ b))) (pw b a a)).symm).trans (pl (a ◇ b) a b c))).symm
  have p1r:=fun (a b c d:G)=>by
    exact ((((p10 c b a c d).trans (p11 b a c d)).symm).trans (((cg (fun t => ((c ◇ (b ◇ a)) ◇ d) ◇ t) (pf a b c)).symm).trans ((h (b ◇ a) (c ◇ (b ◇ a)) d).symm))).symm
  have p1s:=fun (a b c d:G)=>by
    exact ((p0 a a (b ◇ c) d).symm).trans ((((cg (fun t => t ◇ (d ◇ (a ◇ (b ◇ c)))) (pg c b a)).symm).trans (pb a b c a d)).trans (cg (fun t => d ◇ t) (pg c b a)))
  have p1t:=fun (a b c:G)=>by
    exact (((pf (b ◇ a) c c).symm).trans ((((cg (fun t => (c ◇ (b ◇ a)) ◇ t) (pv a b c)).symm).trans (pf (b ◇ a) c (c ◇ b))).trans (cg (fun t => (c ◇ b) ◇ t) (pv a b c)))).symm
  have p1u:=fun (a b c:G)=>by
    exact (((p1o a b c).symm).trans (((cg (fun t => ((a ◇ b) ◇ c) ◇ t) (pz a b)).symm).trans (p1 a b (b ◇ (a ◇ b)) c))).symm
  have p1v:=fun (a b c:G)=>by
    exact (((cg (fun t => (b ◇ ((a ◇ a) ◇ c)) ◇ t) (ph c a (a ◇ ((a ◇ a) ◇ (c ◇ a))))).trans (p1e a c (b ◇ ((a ◇ a) ◇ c)))).symm).trans ((((cg (fun t => (b ◇ ((a ◇ a) ◇ c)) ◇ t) (p6 c a)).symm).trans (pa (a ◇ a) b (a ◇ a) c)).trans (p12 a a c b))
  have p1w:=fun (a b:G)=>by
    exact (((((pc (a ◇ a) b a a).trans (p0 a a a b)).trans (cg (fun t => b ◇ t) (p5 a))).symm).trans ((((p1v a (a ◇ (a ◇ a)) b).symm).trans ((h b (a ◇ (a ◇ a)) ((a ◇ a) ◇ b)).symm)).trans (cg (fun t => b ◇ t) (p17 a b)))).symm
  have p1x:=fun (a b:G)=>by
    exact (((((cg (fun t => (a ◇ b) ◇ t) (pi a b)).trans (p1t b b a)).trans (p1l a b)).symm).trans (((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => b ◇ t) ((h a b b).symm))).symm).trans (p1w b (a ◇ b)))).symm
  have p1y:=fun (a b c d e:G)=>by
    exact (((cg (fun t => (e ◇ ((c ◇ d) ◇ (b ◇ c))) ◇ t) ((h b (c ◇ d) a).symm)).symm).trans (pb b c d e ((c ◇ d) ◇ a))).trans ((p16 b c d e ((c ◇ d) ◇ a)).trans (pc a e b (c ◇ d)))
  have p1z:=fun (a b c:G)=>by
    exact (((((p0 b b (a ◇ a) c).trans (p1s b a a c)).trans (p1e a b c)).symm).trans (((cg (fun t => t ◇ (c ◇ (b ◇ (a ◇ a)))) (pi b a)).symm).trans (p0 a b (a ◇ a) c))).symm
  have p20:=fun (a b c:G)=>by
    exact (((cg (fun t => c ◇ t) ((h a b (a ◇ a)).symm)).symm).trans (p1z a b c)).symm
  have p21:=fun (a b c:G)=>by
    exact (p1e a b c).trans (p20 a b c)
  have p22:=fun (a b c:G)=>by
    exact ((p1m c b c a).symm).trans ((((cg (fun t => (c ◇ (c ◇ (b ◇ c))) ◇ t) ((h a b c).symm)).symm).trans (p1u b c (a ◇ b))).trans ((pc (b ◇ c) a b c).trans (p0 c b c a)))
  have p23:=fun (a b c:G)=>by
    exact (p14 a b c).trans (p22 b c a)
  have p24:=fun (a b c:G)=>by
    exact (p1q a b c).trans (p22 c a b)
  have p25:=fun (a b c:G)=>by
    exact (((cg (fun t => c ◇ t) ((h a b (a ◇ b)).symm)).symm).trans (p24 a b c)).symm
  have p26:=fun (a b c:G)=>by
    exact (((cg (fun t => c ◇ t) ((h b a b).symm)).symm).trans (p25 a b c)).symm
  have p27:=fun (a b c:G)=>by
    exact (p25 a b c).trans (p26 a b c)
  have p28:=fun (a b c:G)=>by
    exact (p22 a b c).trans (p27 b c a)
  have p29:=fun (a b c:G)=>by
    exact (p23 a b c).trans (p27 c a b)
  have p2a:=fun (a b c:G)=>by
    exact (((p27 b c (a ◇ (b ◇ c))).trans (p0 a b c c)).symm).trans ((((p22 (a ◇ (b ◇ c)) b c).symm).trans (p1p a b c)).trans (p27 b c a))
  have p2b:=fun (a b c:G)=>by
    exact ((cg (fun t => c ◇ t) ((h a b c).symm)).symm).trans (p2a a b c)
  have p2c:=fun (a b:G)=>by
    exact (((p1c (a ◇ b) b).trans (p28 b a b)).symm).trans ((((cg (fun t => b ◇ t) (p2b (b ◇ b) a b)).symm).trans (p1n b (a ◇ b))).trans ((p2a a b b).trans (p19 a b)))
  have p2d:=fun (a b c:G)=>by
    exact ((cg (fun t => a ◇ t) (p2c b c)).symm).trans (p28 a b c)
  have p2e:=fun (a b c:G)=>by
    exact ((p2d a a b).symm).trans (p1l a b)
  have p2f:=fun (a b c:G)=>by
    exact (((p2d c b a).symm).trans (p21 a b c)).symm
  have p2g:=fun (a b c:G)=>by
    exact (((cg (fun t => c ◇ t) ((h b c a).symm)).symm).trans (p2b (c ◇ a) b c)).symm
  have p2h:=fun (a b:G)=>by
    exact (((pv a b a).symm).trans ((((p2b (a ◇ b) b a).symm).trans (p27 a b a)).trans (p2e a b (a ◇ (b ◇ (a ◇ b)))))).symm
  have p2i:=fun (a b:G)=>by
    exact (p19 a b).trans (p2h a b)
  have p2j:=fun (a b c:G)=>by
    exact (p2e a b c).trans (p2h a b)
  have p2k:=fun (a b:G)=>by
    exact (p2c a b).trans (p2h a b)
  have p2l:=fun (a b c:G)=>by
    exact ((cg (fun t => a ◇ t) (p2h b c)).symm).trans (p2d a b c)
  have p2m:=fun (a b:G)=>by
    exact (p1x a b).trans (p2h a b)
  have p2n:=fun (a b:G)=>by
    exact (((p2g a b a).symm).trans ((((p2f a b (a ◇ a)).symm).trans (p2b a b (a ◇ a))).trans (cg (fun t => a ◇ t) (pf a a b)))).symm
  have p2o:=fun (a b:G)=>by
    exact (((((cg (fun t => a ◇ t) (p2k a b)).trans (p2l a a b)).trans (p2j a b (a ◇ (b ◇ (a ◇ b))))).symm).trans (((cg (fun t => a ◇ t) (p2h b a)).symm).trans (p2n a b))).symm
  have p2p:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ c)) (p2h a c)).trans (p29 a b c)).symm).trans ((p13 a b c).trans (p2d b a c))).symm
  have p2q:=fun (a b c:G)=>by
    exact (p2a a b c).trans (p2p b a c)
  have p2r:=fun (a b c:G)=>by
    exact (p27 a b c).trans (p2p a c b)
  have p2s:=fun (a b c:G)=>by
    exact (p2b a b c).trans (p2p b a c)
  have p2t:=fun (a b c:G)=>by
    exact ((p1 a b a c).symm).trans (((p2p a ((a ◇ b) ◇ c) b).symm).trans ((h b (a ◇ b) c).symm))
  have p2u:=fun (a b:G)=>by
    exact ((p2t b a a).symm).trans ((h (b ◇ a) a b).symm)
  have p2v:=fun (a b c:G)=>by
    exact (((p2r a b ((b ◇ a) ◇ c)).symm).trans ((h (a ◇ b) (b ◇ a) c).symm)).trans (p2t b a c)
  have p2w:=fun (a b c:G)=>by
    exact ((p2p b (c ◇ a) c).symm).trans (p2g a b c)
  have p2x:=fun (a b c:G)=>by
    exact (((cg (fun t => (c ◇ b) ◇ t) ((h a b c).symm)).symm).trans (p2t b c (a ◇ b))).trans (p2q a b c)
  have p2y:=fun (a b c d:G)=>by
    exact ((cg (fun t => d ◇ t) (pf a b c)).symm).trans (((p2x d (b ◇ a) c).symm).trans (p12 a b c d))
  have p2z:=fun (a b c d:G)=>by
    exact (p1d a b c d).trans (p2y a b d c)
  have p30:=fun (a b c:G)=>by
    exact (((cg (fun t => b ◇ t) (pf a c c)).trans (p2y a c c b)).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => (c ◇ a) ◇ t) ((h c c a).symm))).symm).trans (p2d b (c ◇ a) c))
  have p31:=fun (a b c:G)=>by
    exact (((cg (fun t => b ◇ t) ((h c c a).symm)).symm).trans (p30 a b c)).symm
  have p32:=fun (a b c:G)=>by
    exact (p30 a b c).trans (p31 a b c)
  have p33:=fun (a b c d:G)=>by
    exact ((cg (fun t => d ◇ t) (p2t a a (c ◇ b))).symm).trans (p2y b c (a ◇ a) d)
  have p34:=fun (a b c:G)=>by
    exact ((((((cg (fun t => c ◇ t) (p2o a b)).trans (p2y a b a c)).trans (p2r b a c)).trans (p2p a c b)).symm).trans ((((cg (fun t => c ◇ t) (cg (fun t => a ◇ t) ((h b a a).symm))).symm).trans (p33 a a b c)).trans (pm a b a c))).symm
  have p35:=fun (a b c:G)=>by
    exact ((cg (fun t => c ◇ t) ((h b a a).symm)).symm).trans (p34 a b c)
  have p36:=fun (a b c:G)=>by
    exact ((((p2y a b b c).trans (p32 a c b)).symm).trans (((cg (fun t => c ◇ t) (p1c a b)).symm).trans (p33 b a b c))).symm
  have p37:=fun (a b c:G)=>by
    exact ((cg (fun t => c ◇ t) ((h (b ◇ b) b a).symm)).symm).trans (p36 a b c)
  have p38:=fun (a b c:G)=>by
    exact (((p2v a b c).symm).trans (((p34 a b ((b ◇ a) ◇ c)).symm).trans ((h (a ◇ a) (b ◇ a) c).symm))).symm
  have p39:=fun (a b c:G)=>by
    exact (((cg (fun t => (b ◇ b) ◇ t) ((h a c b).symm)).symm).trans (p38 b c (a ◇ c))).trans ((p2q a c b).trans (p2p b a c))
  have p3a:=fun (a b c:G)=>by
    exact ((p37 a b ((b ◇ a) ◇ c)).symm).trans ((h (b ◇ b) (b ◇ a) c).symm)
  have p3b:=fun (a b c:G)=>by
    exact ((p3a a b c).symm).trans ((h b (b ◇ a) c).symm)
  have p3c:=fun (a b:G)=>by
    exact (((p3b a b b).symm).trans ((h (b ◇ a) b b).symm)).symm
  have p3d:=fun (a b:G)=>by
    exact ((p3c b a).symm).trans ((h a a b).symm)
  have p3e:=fun (a b:G)=>by
    exact (p3c a b).trans (p3d b a)
  have p3f:=fun (a b:G)=>by
    exact ((((p39 b a b).trans (pw a b (b ◇ (a ◇ (b ◇ a))))).symm).trans ((((cg (fun t => (a ◇ a) ◇ t) (p3e a b)).symm).trans (p38 a b (b ◇ b))).trans (cg (fun t => a ◇ t) (p3e a b)))).symm
  have p3g:=fun (a b c:G)=>by
    exact (((((p2p a ((a ◇ b) ◇ c) b).trans (p1 a b a c)).trans (p2t a b c)).symm).trans (((p2d ((a ◇ b) ◇ c) a b).symm).trans (p1f a b c))).symm
  have p3h:=fun (a b:G)=>by
    exact (((p2u b a).symm).trans ((((p3g a b b).symm).trans ((h (a ◇ b) b (b ◇ b)).symm)).trans (p2m a b))).symm
  have p3i:=fun (a b:G)=>by
    exact ((p2h a b).trans (p3h a b)).symm
  have p3j:=fun (a b:G)=>by
    exact ((p35 a b b).symm).trans (((p3i b a).symm).trans ((h a b a).symm))
  have p3k:=fun (a b:G)=>by
    exact (p2i a b).trans (p3h a b)
  have p3l:=fun (a b c:G)=>by
    exact (((p3j a b).symm).trans ((pw a b c).trans (p3h a b))).symm
  have p3m:=fun (a b c:G)=>by
    exact (p2u a b).trans (p3l b a ((b ◇ a) ◇ (a ◇ b)))
  have p3n:=fun (a b:G)=>by
    exact ((p3l b a a).symm).trans ((h a b a).symm)
  have p3o:=fun (a b c:G)=>by
    exact (p3m a b c).trans (p3n a b)
  have p3p:=fun (a b c:G)=>by
    exact (((p3n c (b ◇ a)).symm).trans (pf a b c)).symm
  have p3q:=fun (a b c:G)=>by
    exact (p3k a b).trans (p3l a b ((a ◇ b) ◇ (b ◇ a)))
  have p3r:=fun (a b c:G)=>by
    exact (pg a b c).trans (p3p a b c)
  have p3s:=fun (a b c d:G)=>by
    exact ((cg (fun t => d ◇ t) (p3p a b c)).symm).trans (p2y a b c d)
  have p3t:=fun (a b c:G)=>by
    exact ((p7 b a c).symm).trans (((p3s a b (b ◇ a) c).symm).trans (p3q c (b ◇ a) a))
  have p3u:=fun (a b c d:G)=>by
    exact ((((((cg (fun t => (d ◇ ((b ◇ a) ◇ (c ◇ b))) ◇ t) (p3r a b c)).trans (p1y c c b a d)).trans (p2x d c (b ◇ a))).trans (p3s a b c d)).symm).trans ((((cg (fun t => (d ◇ ((b ◇ a) ◇ (c ◇ b))) ◇ t) (pd a b c)).symm).trans (p0 d (b ◇ a) (c ◇ b) (b ◇ a))).trans ((((p1g c b a d (b ◇ a)).trans (p1r a b c (d ◇ c))).trans (p2s (c ◇ (b ◇ a)) d c)).trans (cg (fun t => (c ◇ (b ◇ a)) ◇ t) (p3n c d))))).symm
  have p3v:=fun (a b:G)=>by
    exact ((p3f a b).trans (p3h a b)).trans (p3l a b ((a ◇ b) ◇ (b ◇ a)))
  have p3w:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ c)) (p3n a c)).symm).trans ((h b c (a ◇ c)).symm)).trans (cg (fun t => b ◇ t) (p3n a c))
  have p3x:=fun (a b c d:G)=>by
    exact ((((cg (fun t => (d ◇ ((b ◇ a) ◇ (b ◇ a))) ◇ t) (p3r a b c)).trans (cg (fun t => t ◇ (c ◇ ((b ◇ a) ◇ c))) (p3t a b d))).trans (p3s a b c (d ◇ ((b ◇ a) ◇ d)))).symm).trans ((((cg (fun t => (d ◇ ((b ◇ a) ◇ (b ◇ a))) ◇ t) (pd a b c)).symm).trans (pa (c ◇ b) d (b ◇ a) (b ◇ a))).trans (((((((cg (fun t => ((b ◇ a) ◇ (c ◇ b)) ◇ t) (p3t a b d)).trans (p2w (c ◇ b) d (b ◇ a))).trans (p16 c b a d (b ◇ a))).trans (p1r a b c (d ◇ c))).trans (p2s (c ◇ (b ◇ a)) d c)).trans (cg (fun t => (c ◇ (b ◇ a)) ◇ t) (p3n c d))).trans (p3u a b c d)))
  have p3y:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ (c ◇ d)) (p3p a b d)).symm).trans (p2z a b c d)
  have p3z:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ (c ◇ a)) (p3o a b a)).symm).trans (p3y a b c a)).trans ((cg (fun t => c ◇ t) (p3l b a ((b ◇ a) ◇ (a ◇ b)))).trans (cg (fun t => c ◇ t) (p3n a b)))
  have p40:=fun (a b c d:G)=>by
    exact ((((((cg (fun t => d ◇ t) (cg (fun t => t ◇ (d ◇ c)) (p3n c (b ◇ a)))).trans (cg (fun t => d ◇ t) (p3z c (b ◇ a) d))).trans (cg (fun t => d ◇ t) (p3s a b c d))).trans (p16 c b a d d)).trans (p3r (b ◇ a) c d)).symm).trans ((((cg (fun t => d ◇ t) (cg (fun t => t ◇ (d ◇ c)) (pe a b c))).symm).trans (pe ((b ◇ a) ◇ (c ◇ b)) c d)).trans (((((((((cg (fun t => (c ◇ ((b ◇ a) ◇ (c ◇ b))) ◇ t) (cg (fun t => d ◇ t) (p3r a b c))).trans (cg (fun t => t ◇ (d ◇ (c ◇ ((b ◇ a) ◇ c)))) (p3r a b c))).trans (cg (fun t => (c ◇ ((b ◇ a) ◇ c)) ◇ t) (p3s a b c d))).trans (p16 c b a d (c ◇ ((b ◇ a) ◇ c)))).trans (pu (b ◇ a) ((b ◇ a) ◇ c) d c)).trans (pl c c (b ◇ a) d)).trans (cg (fun t => d ◇ t) (p3l (b ◇ a) c (((b ◇ a) ◇ c) ◇ (c ◇ (b ◇ a)))))).trans (cg (fun t => d ◇ t) (p3n c (b ◇ a)))).trans (p3s a b c d)))
  have p41:=fun (a b c d:G)=>by
    exact ((((p3w d c (b ◇ a)).trans (p3s a b d c)).symm).trans (((cg (fun t => (d ◇ ((b ◇ a) ◇ d)) ◇ t) ((h c b a).symm)).symm).trans (p3x a b c d))).symm
  have p42:=fun (a b c d:G)=>by
    exact (((cg (fun t => d ◇ t) ((h c b a).symm)).symm).trans (p41 a b c d)).symm
  have p43:=fun (a b c d:G)=>by
    exact ((p40 a b c d).trans (p41 a b c d)).trans (p42 a b c d)
  have p44:=fun (a b c d:G)=>by
    exact (((p42 a b d c).symm).trans ((p41 a b c d).trans (p42 a b c d))).symm
  have p45:=fun (a b c d:G)=>by
    exact (p43 a b c d).trans (p44 a b c d)
  have p46:=fun (a b c d:G)=>by
    exact ((p44 a b ((b ◇ a) ◇ d) c).symm).trans (((p44 a b c ((b ◇ a) ◇ d)).symm).trans ((h c (b ◇ a) d).symm))
  have p47:=fun (a b c:G)=>by
    exact (((cg (fun t => c ◇ t) (cg (fun t => t ◇ c) (p3n a b))).trans (p45 a b a c)).symm).trans ((((cg (fun t => c ◇ t) (cg (fun t => t ◇ c) (p3q b a a))).symm).trans (p45 (a ◇ a) a b c)).trans (((cg (fun t => b ◇ t) (p3q c a (c ◇ (a ◇ (a ◇ a))))).trans (cg (fun t => b ◇ t) (p3n a c))).trans (p44 a c a b)))
  have p48:=fun (a b c d:G)=>by
    exact (((p42 a a b c).trans (p44 a a b c)).symm).trans ((((p41 a a b c).symm).trans (p34 a b c)).trans ((p44 a b a c).trans (p47 a b c)))
  have p49:=fun (a b c:G)=>by
    exact ((((cg (fun t => c ◇ t) (p47 a b c)).trans (p44 (c ◇ a) b a c)).trans (cg (fun t => a ◇ t) (p44 a c b c))).symm).trans ((((cg (fun t => c ◇ t) (p48 a c b a)).symm).trans (p3p (a ◇ a) b c)).trans ((p45 a a b c).trans (p48 a b c (b ◇ (c ◇ (a ◇ a))))))
  have p4a:=fun (a b c:G)=>by
    exact (((cg (fun t => b ◇ t) ((h c (c ◇ b) a).symm)).symm).trans (p49 b ((c ◇ b) ◇ a) c)).trans ((p44 b c ((c ◇ b) ◇ a) b).trans (p46 b c b a))
  have p4b:=fun (a b:G)=>by
    exact ((((p3v b a).trans (p3n a b)).symm).trans (((cg (fun t => b ◇ t) (p3d a b)).symm).trans (p4a a b a))).symm
  exact (calc
    (x ◇ (y ◇ x))=(x ◇ (y ◇ x)):=rfl
    _=(x ◇ ((y ◇ x) ◇ y)):=((p4b y x).trans (p3n x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_56178_to_54898 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_56178_to_54898
