-- Equation4922 → Equation381
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ (x ◇ (z ◇ (y ◇ x))))
-- Conclusion: x ◇ y = (x ◇ z) ◇ y
-- Original submission SHA-256: bc6727d60665fc14e4fee67b957bc1d4c217a033fec669c5bd83fc88f8886865
-- Aurora-accepted correction SHA-256: 0b192a75d3758d2dae82d44d69959a325a0469d12afa4f4052cce2461a4813b8
-- Generator: equational-challenges standalone v2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (x ◇ (z ◇ (y ◇ x))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (x ◇ z) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def submission.bridge:Goal:=by
 intro G _ h
 let K:∀ {a b c d:G},a=b → c=d → a◇c=b◇d:=fun h₁ h₂=>by rw [h₁,h₂]
 let S:∀ {a b:G},a=b → b=a:=@Eq.symm G
 intro x y z
 let l3:=fun (B C D:G)=>
  h B C D
 let l4:=fun (B C D E:G)=>
  let q0:G:=(C◇(C◇(D◇(B◇C))))
  calc (B◇(q0◇(q0◇(E◇C))))
   _=(B◇(q0◇(q0◇(E◇(B◇q0))))):=K rfl (K rfl (K rfl (K rfl ((S (l3 C B D)).symm))))
   _=q0:=(l3 (q0) B E).symm
 let l5x:=fun (A B C:G)=>
  let q0:G:=(B◇(B◇(C◇((A◇B)◇B))))
  calc (A◇B)
   _=(q0◇((A◇B)◇((A◇B)◇(q0◇(q0◇(A◇B)))))):=l3 ((A◇B)) (q0) (q0)
   _=(q0◇((A◇B)◇q0)):=K rfl (K rfl (l4 ((A◇B)) B C A))
 let l5:=fun (B C D:G)=>
  let q0:G:=(B◇(B◇(C◇((D◇B)◇B))))
  have r0:(D◇B)=(q0◇((D◇B)◇q0)):=l5x D B C
  have r1:(D◇B)=(q0◇B):=r0.trans (K rfl ((l3 B (D◇B) C).symm))
  S r1
 let l6:=fun (B C D E:G)=>
  let q0:G:=(B◇(B◇(C◇((D◇B)◇B))))
  calc (q0◇(B◇(B◇(E◇(D◇B)))))
   _=(q0◇(B◇(B◇(E◇(q0◇B))))):=K rfl (K rfl (K rfl (K rfl (S (l5 B C D)))))
   _=B:=(l3 B (q0) E).symm
 let l7:=fun (B C D:G)=>
  calc (B◇((B◇(C◇(D◇B)))◇((B◇(C◇(D◇B)))◇B)))
   _=(B◇((B◇(C◇(D◇B)))◇((B◇(C◇(D◇B)))◇(D◇(B◇(B◇(C◇(D◇B)))))))):=K rfl (K rfl (K rfl ((S (l3 B D C)).symm)))
   _=(B◇(C◇(D◇B))):=(l3 ((B◇(C◇(D◇B)))) B D).symm
 let l8x:=fun (A B C D:G)=>
  let q0:G:=(B◇(B◇(D◇((A◇B)◇B))))
  let q1:G:=((A◇B)◇((A◇B)◇(C◇((q0◇(A◇B))◇(A◇B)))))
  calc (q1◇((A◇B)◇q0))
   _=(q1◇((A◇B)◇((A◇B)◇(q0◇(q0◇(A◇B)))))):=K rfl (K rfl ((l4 ((A◇B)) B D A).symm))
   _=(A◇B):=l6 ((A◇B)) C (q0) (q0)
 let l8:=fun (B C D E:G)=>
  let q0:G:=((B◇C)◇((B◇C)◇(D◇(((C◇(C◇(E◇((B◇C)◇C))))◇(B◇C))◇(B◇C)))))
  have r0:(q0◇((B◇C)◇(C◇(C◇(E◇((B◇C)◇C))))))=(B◇C):=l8x B C D E
  have r1:(q0◇C)=(B◇C):=(K rfl ((l3 C (B◇C) E).symm)).symm.trans r0
  r1
 let l9:=fun (B C D:G)=>
  let q0:G:=((B◇(C◇(D◇B))))
  calc ((B◇(C◇(D◇B)))◇(B◇(B◇(C◇(D◇B)))))
   _=((B◇(C◇(D◇B)))◇(B◇(B◇((B◇(C◇(D◇B)))◇((B◇(C◇(D◇B)))◇B))))):=K rfl (K rfl (S (l7 B C D)))
   _=B:=S (l3 B q0 q0)
 let l10:=fun (B C D E F:G)=>
  let q0:G:=((B◇C)◇((B◇C)◇(D◇(((C◇(C◇(E◇((B◇C)◇C))))◇(B◇C))◇(B◇C)))))
  calc (q0◇(C◇(C◇(F◇(B◇C)))))
   _=(q0◇(C◇(C◇(F◇(q0◇C))))):=K rfl (K rfl (K rfl (K rfl (S (l8 B C D E)))))
   _=C:=(l3 C (q0) F).symm
 let l11:=fun (B C D E F:G)=>
  let q0:G:=((C◇(C◇(D◇(B◇C))))◇((C◇(C◇(D◇(B◇C))))◇(E◇C)))
  calc (B◇(q0◇(q0◇(F◇(C◇(C◇(D◇(B◇C))))))))
   _=(B◇(q0◇(q0◇(F◇(B◇q0))))):=K rfl (K rfl (K rfl (K rfl (S (l4 B C D E)))))
   _=q0:=(l3 (q0) B F).symm
 let l12x:=fun (A B C D:G)=>
  let q0:G:=(A◇(A◇(B◇(C◇A))))
  let q1:G:=((A◇(B◇(C◇A)))◇q0)
  calc ((q0◇(q0◇(D◇(q1◇q0))))◇q0)
   _=q1:=((l5 (q0) D ((A◇(B◇(C◇A))))).symm).symm
   _=A:=l9 A B C
 let l12:=fun (B C D E:G)=>
  let q0:G:=(B◇(B◇(C◇(D◇B))))
  have r0:((q0◇(q0◇(E◇(((B◇(C◇(D◇B)))◇q0)◇q0))))◇q0)=B:=l12x B C D E
  have r1:((q0◇(q0◇(E◇(B◇q0))))◇q0)=B:=(K (K rfl (K rfl (K rfl (K (l9 B C D) rfl)))) rfl).symm.trans r0
  r1
 let l13:=fun (B C D E F:G)=>
  let q0:G:=((B◇(C◇(D◇B)))◇B)
  let q1:G:=(q0◇(q0◇(E◇(((B◇(B◇(F◇(q0◇B))))◇q0)◇q0))))
  let q2:G:=((B◇(C◇(D◇B))))
  calc (q1◇(B◇(B◇(C◇(D◇B)))))
   _=(q1◇(B◇(B◇((B◇(C◇(D◇B)))◇q0)))):=K rfl (K rfl (S (l7 B C D)))
   _=B:=l10 q2 B E F q2
 let l14:=fun (B C D E:G)=>
  let q0:G:=(C◇(C◇(D◇(B◇C))))
  let q1:G:=(q0◇(q0◇(B◇(C◇q0))))
  calc (B◇((q0◇(q0◇(E◇C)))◇((q0◇(q0◇(E◇C)))◇C)))
   _=(B◇((q0◇(q0◇(E◇C)))◇((q0◇(q0◇(E◇C)))◇(q1◇q0)))):=K rfl (K rfl (K rfl (S (l12 C D B B))))
   _=(q0◇(q0◇(E◇C))):=l11 B C D E (q1)
 let l15:=fun (B C D E F:G)=>
  let q0:G:=((C◇(C◇(D◇(E◇C))))◇((C◇(C◇(D◇(E◇C))))◇(F◇(B◇(C◇(C◇(D◇(E◇C))))))))
  let q1:G:=(C◇(C◇(D◇(E◇C))))
  calc (B◇(q0◇(q0◇C)))
   _=(B◇(q0◇(q0◇((C◇(D◇(E◇C)))◇q1)))):=K rfl (K rfl (K rfl (S (l9 C D E))))
   _=q0:=l4 B (q1) F ((C◇(D◇(E◇C))))
 let l16:=fun (B C D E F:G)=>
  have p9:∀ (x y z u:G),(x◇(((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y)))◇(((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y)))◇y)))=((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y))):=by
   intro x y z u
   exact l14 x y z u
  have p7:∀ (x y z u w:G),((((x◇(y◇(z◇x)))◇x)◇(((x◇(y◇(z◇x)))◇x)◇(u◇(((x◇(x◇(w◇(((x◇(y◇(z◇x)))◇x)◇x))))◇((x◇(y◇(z◇x)))◇x))◇((x◇(y◇(z◇x)))◇x)))))◇(x◇(x◇(y◇(z◇x)))))=x:=by
   intro x y z u w
   exact l13 x y z u w
  have p6:∀ (x y z u:G),(x◇((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y))))=(y◇(y◇(z◇(x◇y)))):=by
   intro x y z u
   exact l4 x y z u
  have p21x:∀ (A B C D E:G),(((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)◇(((A◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)))◇A)◇(D◇(((A◇(A◇(E◇(((A◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)))◇A)◇A))))◇((A◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)))◇A))◇((A◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)))◇A)))))◇(A◇(A◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)))))=A:=by
   intro A B C D E
   let s0:G:=((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))
   let s1:G:=((A◇(s0◇(s0◇A)))◇A)
   let s2:G:=(s1◇(D◇(((A◇(A◇(E◇(s1◇A))))◇s1)◇s1)))
   let s3:G:=(A◇(A◇(s0◇(s0◇A))))
   calc (((s0◇A)◇s2)◇s3)
    _=((s1◇s2)◇s3):=K (K (K (S (p9 A A B C)) rfl) rfl) rfl
    _=A:=p7 A (s0) (s0) D E
  have p21:∀ (x y z u w:G),(((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)◇((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)◇(u◇(((x◇(x◇(w◇((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)◇x))))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)))))◇(x◇(x◇(y◇(x◇x)))))=x:=by
   intro x y z u w
   simpa only [p9,p9,p9,p9,p9,p6] using (p21x x y z u w)
  p21 B C D E F
 let l17x:=fun (A B C D:G)=>
  let q0:G:=(A◇(A◇(B◇(C◇A))))
  let q1:G:=(q0◇(D◇((A◇(B◇(C◇A)))◇q0)))
  calc ((q0◇(D◇A))◇(q0◇q1))
   _=(q1◇(q0◇q1)):=K (K rfl (K rfl (S (l9 A B C)))) rfl
   _=q0:=l9 (q0) D ((A◇(B◇(C◇A))))
 let l17:=fun (B C D E:G)=>
  let q0:G:=(B◇(B◇(C◇(D◇B))))
  have r0:((q0◇(E◇B))◇(q0◇(q0◇(E◇((B◇(C◇(D◇B)))◇q0)))))=q0:=l17x B C D E
  have r1:((q0◇(E◇B))◇(q0◇(q0◇(E◇B))))=q0:=(K rfl (K rfl (K rfl (K rfl (l9 B C D))))).symm.trans r0
  r1
 have l18:∀ (B C D E F X6:G),(((((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))◇B)◇((((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))◇B)◇(E◇(((B◇(B◇(F◇((((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))◇B)◇B))))◇(((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))◇B))◇(((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))◇B)))))◇(((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(X6◇B)))◇(((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(X6◇B)))◇B)))=((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(X6◇B))):=by
  intro B C D E F X6
  let q0:G:=(((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))◇B)
  simpa only [q0,l16] using (l15 ((q0◇(q0◇(E◇(((B◇(B◇(F◇(q0◇B))))◇q0)◇q0))))) B C B X6)
 let l19:=fun (B C D E F X6:G)=>
  let q0:G:=(((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))◇B)
  let q1:G:=(q0◇(q0◇(E◇(((B◇(B◇(F◇(q0◇B))))◇q0)◇q0))))
  let q2:G:=(B◇(B◇(C◇(B◇B))))
  calc (q1◇(q2◇(q2◇(X6◇B))))
   _=(q1◇(q2◇(q2◇(X6◇(q1◇q2))))):=K rfl (K rfl (K rfl (K rfl (S (l16 B C D E F)))))
   _=q2:=(l3 (q2) (q1) X6).symm
 let l20:=fun (B C D:G)=>
  let q0:G:=(B◇(B◇(C◇(B◇B))))
  calc ((q0◇(q0◇(D◇B)))◇q0)
   _=((q0◇(q0◇(D◇(B◇q0))))◇q0):=K (K rfl (K rfl (K rfl ((S (l3 B B C)).symm)))) rfl
   _=B:=l12 B C B D
 let l21:=fun (B C D E F:G)=>
  have p9:∀ (x y z u w v5:G),(((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)◇((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)◇(u◇(((x◇(x◇(w◇((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)◇x))))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)))))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(v5◇x)))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(v5◇x)))◇x)))=((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(v5◇x))):=by
   intro x y z u w v5
   exact l18 x y z u w v5
  have p7:∀ (x y z u:G),(((x◇(x◇(y◇(z◇x))))◇(u◇x))◇((x◇(x◇(y◇(z◇x))))◇((x◇(x◇(y◇(z◇x))))◇(u◇x))))=(x◇(x◇(y◇(z◇x)))):=by
   intro x y z u
   exact l17 x y z u
  have p8:∀ (x y z u w v5:G),(((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)◇((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)◇(u◇(((x◇(x◇(w◇((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)◇x))))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)))))◇((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(v5◇x))))=(x◇(x◇(y◇(x◇x)))):=by
   intro x y z u w v5
   exact l19 x y z u w v5
  have p6:∀ (x y z:G),(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(x◇(x◇(y◇(x◇x)))))=x:=by
   intro x y z
   exact l20 x y z
  have p16x:∀ (A B C D E:G),(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)◇((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)◇(D◇(((A◇(A◇(E◇((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)◇A))))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)))))◇(((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)◇((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)◇(D◇(((A◇(A◇(E◇((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)◇A))))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)))))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)))))=((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)◇((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)◇(D◇(((A◇(A◇(E◇((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A)◇A))))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A))))):=by
   intro A B C D E
   let s0:G:=((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))
   let s1:G:=((s0◇A)◇((s0◇A)◇(D◇(((A◇(A◇(E◇((s0◇A)◇A))))◇(s0◇A))◇(s0◇A)))))
   let s2:G:=(s1◇(s1◇(s0◇(s0◇A))))
   calc (s0◇s2)
    _=((s1◇(s0◇(s0◇A)))◇s2):=K (S (p9 A B C D E C)) rfl
    _=s1:=p7 ((s0◇A)) D (((A◇(A◇(E◇((s0◇A)◇A))))◇(s0◇A))) (s0)
  have p16:∀ (x y z u w:G),((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)◇((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)◇(u◇(((x◇(x◇(w◇((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)◇x))))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)))))=x:=by
   intro x y z u w
   let s0:G:=((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))
   let s1:G:=((s0◇x)◇((s0◇x)◇(u◇(((x◇(x◇(w◇((s0◇x)◇x))))◇(s0◇x))◇(s0◇x)))))
   have r0:(s0◇(s1◇(s1◇(s0◇(s0◇x)))))=s1:=p16x x y z u w
   have r1:(s0◇(s1◇s0))=s1:=(K rfl (K rfl (p9 x y z u w z))).symm.trans r0
   have r2:(s0◇(x◇(x◇(y◇(x◇x)))))=s1:=(K rfl (p8 x y z u w z)).symm.trans r1
   have r3:x=s1:=(S (p6 x y z)).trans r2
   exact S r3
  p16 B C D E F
 let l22:=fun (B C D:G)=>
  let q0:G:=((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))
  calc (q0◇B)
   _=(((q0◇B)◇((q0◇B)◇(B◇(((B◇(B◇(B◇((q0◇B)◇B))))◇(q0◇B))◇(q0◇B)))))◇B):=(l8 (q0) B B B).symm
   _=(B◇B):=K (l21 B C D B B) rfl
 let l23:=fun (B C D E F:G)=>
  let q0:G:=((C◇(C◇(D◇(B◇C))))◇((C◇(C◇(D◇(B◇C))))◇(E◇C)))
  calc (B◇((q0◇(q0◇C))◇((q0◇(q0◇C))◇(F◇q0))))
   _=(B◇((q0◇(q0◇C))◇((q0◇(q0◇C))◇(F◇(B◇(q0◇(q0◇C))))))):=K rfl (K rfl (K rfl (K rfl (S (l14 B C D E)))))
   _=(q0◇(q0◇C)):=(l3 ((q0◇(q0◇C))) B F).symm
 let l24:=fun (B C D:G)=>
  let q0:G:=(((B◇(B◇(B◇(B◇B))))◇((B◇(B◇(B◇(B◇B))))◇(B◇B)))◇B)
  let q1:G:=(C◇(((B◇(B◇(D◇(q0◇B))))◇q0)◇q0))
  let q2:G:=(B◇(B◇(D◇((B◇B)◇B))))
  have r0:(q0◇(q0◇q1))=B:=l21 B B B C D
  have r1:((B◇B)◇(q0◇q1))=B:=(K (l22 B B B) rfl).symm.trans r0
  have r2:((B◇B)◇((B◇B)◇q1))=B:=(K rfl (K (l22 B B B) rfl)).symm.trans r1
  have r3:((B◇B)◇((B◇B)◇(C◇((q2◇q0)◇q0))))=B:=(K rfl (K rfl (K rfl (K (K (K rfl (K rfl (K rfl (K (l22 B B B) rfl)))) rfl) rfl)))).symm.trans r2
  have r4:((B◇B)◇((B◇B)◇(C◇((q2◇(B◇B))◇q0))))=B:=(K rfl (K rfl (K rfl (K (K rfl (l22 B B B)) rfl)))).symm.trans r3
  have r5:((B◇B)◇((B◇B)◇(C◇((q2◇(B◇B))◇(B◇B)))))=B:=(K rfl (K rfl (K rfl (K rfl (l22 B B B))))).symm.trans r4
  r5
 let l25:=fun (B C D E:G)=>
  let q0:G:=((C◇(C◇(D◇(B◇C))))◇((C◇(C◇(D◇(B◇C))))◇(E◇C)))
  let q1:G:=(C◇(C◇(D◇(B◇C))))
  calc (B◇((q0◇(q0◇C))◇((q0◇(q0◇C))◇q1)))
   _=(B◇((q0◇(q0◇C))◇((q0◇(q0◇C))◇((q1◇(E◇C))◇q0)))):=K rfl (K rfl (K rfl (S (l17 C D B E))))
   _=(q0◇(q0◇C)):=l23 B C D E ((q1◇(E◇C)))
 let l26:=fun (B C:G)=>
  let q0:G:=(B◇(B◇(C◇((B◇B)◇B))))
  calc (q0◇(B◇B))
   _=(((B◇B)◇((B◇B)◇(B◇((q0◇(B◇B))◇(B◇B)))))◇(B◇B)):=(l5 ((B◇B)) B (q0)).symm
   _=(B◇(B◇B)):=K (l24 B B C) rfl
 let l27:=fun (B C D E F:G)=>
  have p4:∀ (x y z:G),((x◇(x◇(y◇((z◇x)◇x))))◇x)=(z◇x):=by
   intro x y z
   exact l5 x y z
  have p6:∀ (x y z u:G),(x◇((((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y)))◇(((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y)))◇y))◇((((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y)))◇(((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y)))◇y))◇(y◇(y◇(z◇(x◇y)))))))=(((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y)))◇(((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y)))◇y)):=by
   intro x y z u
   exact l25 x y z u
  have p9x:∀ (A B C D E:G),((A◇(A◇(B◇((C◇A)◇A))))◇((((A◇(A◇(D◇(C◇A))))◇((A◇(A◇(D◇((A◇(A◇(B◇((C◇A)◇A))))◇A))))◇(E◇A)))◇(((A◇(A◇(D◇((A◇(A◇(B◇((C◇A)◇A))))◇A))))◇((A◇(A◇(D◇((A◇(A◇(B◇((C◇A)◇A))))◇A))))◇(E◇A)))◇A))◇((((A◇(A◇(D◇((A◇(A◇(B◇((C◇A)◇A))))◇A))))◇((A◇(A◇(D◇((A◇(A◇(B◇((C◇A)◇A))))◇A))))◇(E◇A)))◇(((A◇(A◇(D◇((A◇(A◇(B◇((C◇A)◇A))))◇A))))◇((A◇(A◇(D◇((A◇(A◇(B◇((C◇A)◇A))))◇A))))◇(E◇A)))◇A))◇(A◇(A◇(D◇((A◇(A◇(B◇((C◇A)◇A))))◇A)))))))=(((A◇(A◇(D◇((A◇(A◇(B◇((C◇A)◇A))))◇A))))◇((A◇(A◇(D◇((A◇(A◇(B◇((C◇A)◇A))))◇A))))◇(E◇A)))◇(((A◇(A◇(D◇((A◇(A◇(B◇((C◇A)◇A))))◇A))))◇((A◇(A◇(D◇((A◇(A◇(B◇((C◇A)◇A))))◇A))))◇(E◇A)))◇A)):=by
   intro A B C D E
   let s0:G:=(A◇(A◇(D◇((A◇(A◇(B◇((C◇A)◇A))))◇A))))
   let s1:G:=((s0◇(s0◇(E◇A)))◇((s0◇(s0◇(E◇A)))◇A))
   let s2:G:=(A◇(A◇(B◇((C◇A)◇A))))
   calc (s2◇((((A◇(A◇(D◇(C◇A))))◇(s0◇(E◇A)))◇((s0◇(s0◇(E◇A)))◇A))◇(s1◇s0)))
    _=(s2◇(s1◇(s1◇s0))):=K rfl (K (K (K (K rfl (K rfl (K rfl (S (p4 A B C))))) rfl) rfl) rfl)
    _=s1:=p6 (s2) A D E
  have p9:∀ (x y z u w:G),((x◇(x◇(y◇((z◇x)◇x))))◇((((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇(((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇x))◇((((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇(((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇x))◇(x◇(x◇(u◇(z◇x)))))))=(((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇(((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇x)):=by
   intro x y z u w
   let s0:G:=(x◇(x◇(u◇((x◇(x◇(y◇((z◇x)◇x))))◇x))))
   let s1:G:=((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))
   let s2:G:=((s0◇(s0◇(w◇x)))◇((s0◇(s0◇(w◇x)))◇x))
   let s3:G:=((x◇(x◇(y◇((z◇x)◇x))))◇((s1◇(s1◇x))◇((s1◇(s1◇x))◇(x◇(x◇(u◇(z◇x)))))))
   let s4:G:=((x◇(x◇(u◇(z◇x))))◇(s0◇(w◇x)))
   let s5:G:=(x◇(x◇(y◇((z◇x)◇x))))
   let s6:G:=((s0◇(s0◇(w◇x)))◇x)
   have r0:(s5◇((s4◇s6)◇(s2◇s0)))=s2:=p9x x y z u w
   have r1:(s5◇((s1◇s6)◇(s2◇s0)))=s2:=(K rfl (K (K (K rfl (K (K rfl (K rfl (K rfl (p4 x y z)))) rfl)) rfl) rfl)).symm.trans r0
   have r2:(s5◇((s1◇(s4◇x))◇(s2◇s0)))=s2:=(K rfl (K (K rfl (K (K (K rfl (K rfl (K rfl (p4 x y z)))) rfl) rfl)) rfl)).symm.trans r1
   have r3:(s5◇((s1◇(s1◇x))◇(s2◇s0)))=s2:=(K rfl (K (K rfl (K (K rfl (K (K rfl (K rfl (K rfl (p4 x y z)))) rfl)) rfl)) rfl)).symm.trans r2
   have r4:(s5◇((s1◇(s1◇x))◇((s4◇s6)◇s0)))=s2:=(K rfl (K rfl (K (K (K (K rfl (K rfl (K rfl (p4 x y z)))) rfl) rfl) rfl))).symm.trans r3
   have r5:(s5◇((s1◇(s1◇x))◇((s1◇s6)◇s0)))=s2:=(K rfl (K rfl (K (K (K rfl (K (K rfl (K rfl (K rfl (p4 x y z)))) rfl)) rfl) rfl))).symm.trans r4
   have r6:(s5◇((s1◇(s1◇x))◇((s1◇(s4◇x))◇s0)))=s2:=(K rfl (K rfl (K (K rfl (K (K (K rfl (K rfl (K rfl (p4 x y z)))) rfl) rfl)) rfl))).symm.trans r5
   have r7:(s5◇((s1◇(s1◇x))◇((s1◇(s1◇x))◇s0)))=s2:=(K rfl (K rfl (K (K rfl (K (K rfl (K (K rfl (K rfl (K rfl (p4 x y z)))) rfl)) rfl)) rfl))).symm.trans r6
   have r8:s3=s2:=(K rfl (K rfl (K rfl (K rfl (K rfl (K rfl (p4 x y z))))))).symm.trans r7
   have r9:s3=(s4◇s6):=r8.trans (K (K (K rfl (K rfl (K rfl (p4 x y z)))) rfl) rfl)
   have r10:s3=(s1◇s6):=r9.trans (K (K rfl (K (K rfl (K rfl (K rfl (p4 x y z)))) rfl)) rfl)
   have r11:s3=(s1◇(s4◇x)):=r10.trans (K rfl (K (K (K rfl (K rfl (K rfl (p4 x y z)))) rfl) rfl))
   have r12:s3=(s1◇(s1◇x)):=r11.trans (K rfl (K (K rfl (K (K rfl (K rfl (K rfl (p4 x y z)))) rfl)) rfl))
   exact r12
  p9 B C D E F
 let l28:=fun (B C:G)=>
  calc ((B◇B)◇((B◇B)◇(C◇((B◇(B◇B))◇(B◇B)))))
   _=((B◇B)◇((B◇B)◇(C◇(((B◇(B◇(B◇((B◇B)◇B))))◇(B◇B))◇(B◇B))))):=K rfl (K rfl (K rfl (K (S (l26 B B)) rfl)))
   _=B:=l24 B C B
 let l29x:=fun (A B C D E:G)=>
  let q0:G:=((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))
  let q1:G:=(A◇(A◇(D◇(q0◇A))))
  calc (q0◇((A◇(A◇(D◇(A◇A))))◇(q1◇(E◇A))))
   _=(q0◇(q1◇(q1◇(E◇A)))):=K rfl (K (K rfl (K rfl (K rfl (S (l22 A B C))))) rfl)
   _=q1:=l4 (q0) A D E
 let l29:=fun (B C D E F:G)=>
  let q0:G:=((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))
  let q1:G:=(B◇(B◇(E◇(B◇B))))
  let q2:G:=(B◇(B◇(E◇(q0◇B))))
  let q3:G:=(q0◇(q1◇(q1◇(F◇B))))
  have r0:(q0◇(q1◇(q2◇(F◇B))))=q2:=l29x B C D E F
  have r1:q3=q2:=(K rfl (K rfl (K (K rfl (K rfl (K rfl (l22 B C D)))) rfl))).symm.trans r0
  have r2:q3=q1:=r1.trans (K rfl (K rfl (K rfl (l22 B C D))))
  r2
 let l30:=fun (B C D E:G)=>
  let q0:G:=((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))
  calc (q0◇(B◇(B◇(E◇(B◇B)))))
   _=(q0◇(B◇(B◇(E◇(q0◇B))))):=K rfl (K rfl (K rfl (K rfl (S (l22 B C D)))))
   _=B:=(l3 B (q0) E).symm
 let l31:=fun (B C D:G)=>
  have p5:∀ (x y:G),((x◇x)◇((x◇x)◇(y◇((x◇(x◇x))◇(x◇x)))))=x:=by
   intro x y
   exact l28 x y
  have p8:∀ (x y z u w:G),((x◇(x◇(y◇((z◇x)◇x))))◇((((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇(((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇x))◇((((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇(((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇x))◇(x◇(x◇(u◇(z◇x)))))))=(((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇(((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇x)):=by
   intro x y z u w
   exact l27 x y z u w
  have p6:∀ (x y z:G),(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)=(x◇x):=by
   intro x y z
   exact l22 x y z
  have p11x:∀ (A B C D:G),(((A◇A)◇((A◇A)◇(B◇(((A◇(A◇A))◇(A◇A))◇(A◇A)))))◇(((A◇(((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(D◇(A◇A))))◇((((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(D◇(A◇A))))◇(A◇A)))◇(((((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(D◇(A◇A))))◇((((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(D◇(A◇A))))◇(A◇A)))◇((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A))))))))=((((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(D◇(A◇A))))◇((((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(D◇(A◇A))))◇(A◇A))):=by
   intro A B C D
   let s0:G:=((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))
   let s1:G:=((s0◇(s0◇(D◇(A◇A))))◇((s0◇(s0◇(D◇(A◇A))))◇(A◇A)))
   let s2:G:=((A◇A)◇((A◇A)◇(B◇(((A◇(A◇A))◇(A◇A))◇(A◇A)))))
   calc (s2◇(((A◇(s0◇(D◇(A◇A))))◇((s0◇(s0◇(D◇(A◇A))))◇(A◇A)))◇(s1◇s0)))
    _=(s2◇(s1◇(s1◇s0))):=K rfl (K (K (K (S (p5 A C)) rfl) rfl) rfl)
    _=s1:=p8 ((A◇A)) B ((A◇(A◇A))) C D
  have p11:∀ (x y z:G),(((x◇x)◇((x◇x)◇(y◇(((x◇(x◇x))◇(x◇x))◇(x◇x)))))◇(((x◇(x◇(z◇(x◇x))))◇((x◇(x◇(z◇(x◇x))))◇(x◇x)))◇(x◇x)))=((x◇(x◇(z◇(x◇x))))◇((x◇(x◇(z◇(x◇x))))◇(x◇x))):=by
   intro x y z
   let s0:G:=(((x◇x)◇((x◇x)◇(x◇((x◇(x◇x))◇(x◇x)))))◇(((x◇x)◇((x◇x)◇(x◇((x◇(x◇x))◇(x◇x)))))◇(z◇(x◇x))))
   let s1:G:=((x◇x)◇((x◇x)◇(y◇(((x◇(x◇x))◇(x◇x))◇(x◇x)))))
   let s2:G:=((x◇(x◇(z◇(x◇x))))◇((x◇(x◇(z◇(x◇x))))◇(x◇x)))
   let s3:G:=((x◇x)◇((x◇x)◇(x◇((x◇(x◇x))◇(x◇x)))))
   let s4:G:=((x◇(x◇(z◇(x◇x))))◇((x◇(s3◇(z◇(x◇x))))◇(x◇x)))
   let s5:G:=((x◇(s3◇(z◇(x◇x))))◇(s0◇(x◇x)))
   let s6:G:=((x◇(x◇(z◇(x◇x))))◇(s0◇(x◇x)))
   let s7:G:=((s0◇(s0◇(x◇x)))◇s3)
   have r0:(s1◇(s5◇s7))=(s0◇(s0◇(x◇x))):=p11x x y x z
   have r1:(s1◇(s6◇s7))=(s0◇(s0◇(x◇x))):=(K rfl (K (K (K rfl (K (p5 x x) rfl)) rfl) rfl)).symm.trans r0
   have r2:(s1◇(s4◇s7))=(s0◇(s0◇(x◇x))):=(K rfl (K (K rfl (K (K (p5 x x) rfl) rfl)) rfl)).symm.trans r1
   have r3:(s1◇(s2◇s7))=(s0◇(s0◇(x◇x))):=(K rfl (K (K rfl (K (K rfl (K (p5 x x) rfl)) rfl)) rfl)).symm.trans r2
   have r4:(s1◇(s2◇(s5◇s3)))=(s0◇(s0◇(x◇x))):=(K rfl (K rfl (K (K (K (p5 x x) rfl) rfl) rfl))).symm.trans r3
   have r5:(s1◇(s2◇(s6◇s3)))=(s0◇(s0◇(x◇x))):=(K rfl (K rfl (K (K (K rfl (K (p5 x x) rfl)) rfl) rfl))).symm.trans r4
   have r6:(s1◇(s2◇(s4◇s3)))=(s0◇(s0◇(x◇x))):=(K rfl (K rfl (K (K rfl (K (K (p5 x x) rfl) rfl)) rfl))).symm.trans r5
   have r7:(s1◇(s2◇(s2◇s3)))=(s0◇(s0◇(x◇x))):=(K rfl (K rfl (K (K rfl (K (K rfl (K (p5 x x) rfl)) rfl)) rfl))).symm.trans r6
   have r8:(s1◇(s2◇(s2◇x)))=(s0◇(s0◇(x◇x))):=(K rfl (K rfl (K rfl (p5 x x)))).symm.trans r7
   have r9:(s1◇(s2◇(x◇x)))=(s0◇(s0◇(x◇x))):=(K rfl (K rfl (p6 x z x))).symm.trans r8
   have r10:(s1◇(s2◇(x◇x)))=s5:=r9.trans (K (K (p5 x x) rfl) rfl)
   have r11:(s1◇(s2◇(x◇x)))=s6:=r10.trans (K (K rfl (K (p5 x x) rfl)) rfl)
   have r12:(s1◇(s2◇(x◇x)))=s4:=r11.trans (K rfl (K (K (p5 x x) rfl) rfl))
   have r13:(s1◇(s2◇(x◇x)))=s2:=r12.trans (K rfl (K (K rfl (K (p5 x x) rfl)) rfl))
   exact r13
  p11 B C D
 let l32:=fun (B C D E:G)=>
  have p9:∀ (x y z u w:G),(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇((x◇(x◇(u◇(x◇x))))◇((x◇(x◇(u◇(x◇x))))◇(w◇x))))=(x◇(x◇(u◇(x◇x)))):=by
   intro x y z u w
   exact l29 x y z u w
  have p7:∀ (x y:G),((x◇x)◇((x◇x)◇(y◇((x◇(x◇x))◇(x◇x)))))=x:=by
   intro x y
   exact l28 x y
  have p8:∀ (x y z u:G),(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(x◇(x◇(u◇(x◇x)))))=x:=by
   intro x y z u
   exact l30 x y z u
  have p6:∀ (x y z:G),(x◇(y◇(y◇(z◇(x◇y)))))=y:=by
   intro x y z
   exact S (l3 y x z)
  have p19x:∀ (A B C D:G),((A◇(A◇(B◇(A◇A))))◇((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A))))◇(D◇((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A))))))))=((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A))):=by
   intro A B C D
   let s0:G:=((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))
   let s1:G:=((s0◇s0)◇(D◇((s0◇(s0◇s0))◇(s0◇s0))))
   calc ((A◇(A◇(B◇(A◇A))))◇s1)
    _=((s0◇s0)◇s1):=K (S (p9 A B C B C)) rfl
    _=s0:=p7 (s0) D
  have p19:∀ (x y z u:G),((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))=((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(u◇x))):=by
   intro x y z u
   let s0:G:=((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(u◇x)))
   let s1:G:=(x◇(x◇(y◇(x◇x))))
   let s2:G:=(z◇((s0◇(s0◇s0))◇(s0◇s0)))
   have r0:(s1◇((s0◇s0)◇s2))=s0:=p19x x y u z
   have r1:(s1◇(s1◇s2))=s0:=(K rfl (K (p9 x y u y u) rfl)).symm.trans r0
   have r2:(s1◇(s1◇(z◇((s0◇s1)◇(s0◇s0)))))=s0:=(K rfl (K rfl (K rfl (K (K rfl (p9 x y u y u)) rfl)))).symm.trans r1
   have r3:(s1◇(s1◇(z◇(x◇(s0◇s0)))))=s0:=(K rfl (K rfl (K rfl (K (p8 x y u y) rfl)))).symm.trans r2
   have r4:(s1◇(s1◇(z◇(x◇s1))))=s0:=(K rfl (K rfl (K rfl (K rfl (p9 x y u y u))))).symm.trans r3
   have r5:(s1◇(s1◇(z◇x)))=s0:=(K rfl (K rfl (K rfl (p6 x x y)))).symm.trans r4
   exact r5
  p19 B C D E
 let l33x:=fun (A B C D E F:G)=>
  let q0:G:=(A◇(A◇(D◇(C◇A))))
  let q1:G:=(A◇(A◇(B◇((C◇A)◇A))))
  let q2:G:=(q0◇(q0◇(E◇(q1◇q0))))
  calc (q1◇((q0◇(q0◇(E◇A)))◇(q2◇(F◇q0))))
   _=(q1◇(q2◇(q2◇(F◇q0)))):=K rfl (K (K rfl (K rfl (K rfl (S (l6 A B C D))))) rfl)
   _=q2:=l4 (q1) (q0) E F
 let l33:=fun (B C D E F X6:G)=>
  let q0:G:=(B◇(B◇(E◇(D◇B))))
  let q1:G:=(B◇(B◇(C◇((D◇B)◇B))))
  let q2:G:=(q1◇((q0◇(q0◇(F◇B)))◇((q0◇(q0◇(F◇B)))◇(X6◇q0))))
  let q3:G:=(q0◇(q0◇(F◇(q1◇q0))))
  have r0:(q1◇((q0◇(q0◇(F◇B)))◇(q3◇(X6◇q0))))=q3:=l33x B C D E F X6
  have r1:q2=q3:=(K rfl (K rfl (K (K rfl (K rfl (K rfl (l6 B C D E)))) rfl))).symm.trans r0
  have r2:q2=(q0◇(q0◇(F◇B))):=r1.trans (K rfl (K rfl (K rfl (l6 B C D E))))
  r2
 let l34:=fun (B C D E:G)=>
  let q0:G:=(B◇(B◇(D◇(B◇B))))
  let q1:G:=((B◇B)◇((B◇B)◇(C◇(((B◇(B◇B))◇(B◇B))◇(B◇B)))))
  calc (q1◇((q0◇(q0◇(E◇B)))◇(B◇B)))
   _=(q1◇((q0◇(q0◇(B◇B)))◇(B◇B))):=K rfl (K (l32 B D E B) rfl)
   _=(q0◇(q0◇(B◇B))):=l31 B C D
   _=(q0◇(q0◇(E◇B))):=S (l32 B D E B)
 let l35:=fun (B C D E:G)=>
  have p4:∀ (x y:G),((x◇x)◇((x◇x)◇(y◇((x◇(x◇x))◇(x◇x)))))=x:=by
   intro x y
   exact l28 x y
  have p6:∀ (x y z u w v5:G),((x◇(x◇(y◇((z◇x)◇x))))◇(((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇(((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇(v5◇(x◇(x◇(u◇(z◇x))))))))=((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x))):=by
   intro x y z u w v5
   exact l33 x y z u w v5
  have p9x:∀ (A B C D E:G),(((A◇A)◇((A◇A)◇(B◇(((A◇(A◇A))◇(A◇A))◇(A◇A)))))◇((A◇(((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(D◇(A◇A))))◇((((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(D◇(A◇A))))◇(E◇((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))))))=(((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(D◇(A◇A)))):=by
   intro A B C D E
   let s0:G:=((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))
   let s1:G:=(s0◇(s0◇(D◇(A◇A))))
   let s2:G:=((A◇A)◇((A◇A)◇(B◇(((A◇(A◇A))◇(A◇A))◇(A◇A)))))
   calc (s2◇((A◇(s0◇(D◇(A◇A))))◇(s1◇(E◇s0))))
    _=(s2◇(s1◇(s1◇(E◇s0)))):=K rfl (K (K (S (p4 A C)) rfl) rfl)
    _=s1:=p6 ((A◇A)) B ((A◇(A◇A))) C D E
  have p9:∀ (x y z u:G),(((x◇x)◇((x◇x)◇(y◇(((x◇(x◇x))◇(x◇x))◇(x◇x)))))◇((x◇(x◇(z◇(x◇x))))◇((x◇(x◇(z◇(x◇x))))◇(u◇x))))=(x◇(x◇(z◇(x◇x)))):=by
   intro x y z u
   let s0:G:=((x◇x)◇((x◇x)◇(x◇((x◇(x◇x))◇(x◇x)))))
   let s1:G:=((x◇x)◇((x◇x)◇(y◇(((x◇(x◇x))◇(x◇x))◇(x◇x)))))
   let s2:G:=(x◇(x◇(z◇(x◇x))))
   let s3:G:=(s0◇(s0◇(z◇(x◇x))))
   let s4:G:=(s1◇(s2◇(s2◇(u◇x))))
   let s5:G:=(x◇(s0◇(z◇(x◇x))))
   have r0:(s1◇(s5◇(s3◇(u◇s0))))=s3:=p9x x y x z u
   have r1:(s1◇(s2◇(s3◇(u◇s0))))=s3:=(K rfl (K (K rfl (K (p4 x x) rfl)) rfl)).symm.trans r0
   have r2:(s1◇(s2◇(s5◇(u◇s0))))=s3:=(K rfl (K rfl (K (K (p4 x x) rfl) rfl))).symm.trans r1
   have r3:(s1◇(s2◇(s2◇(u◇s0))))=s3:=(K rfl (K rfl (K (K rfl (K (p4 x x) rfl)) rfl))).symm.trans r2
   have r4:s4=s3:=(K rfl (K rfl (K rfl (K rfl (p4 x x))))).symm.trans r3
   have r5:s4=s5:=r4.trans (K (p4 x x) rfl)
   have r6:s4=s2:=r5.trans (K rfl (K (p4 x x) rfl))
   exact r6
  p9 B C D E
 let l36x:=fun (A B C D:G)=>
  let q0:G:=((A◇A)◇((A◇A)◇(B◇(((A◇(A◇A))◇(A◇A))◇(A◇A)))))
  let q1:G:=((A◇(A◇(C◇(A◇A))))◇((A◇(A◇(C◇(A◇A))))◇(D◇A)))
  let q2:G:=((A◇(A◇A))◇(A◇A))
  calc (q2◇(q0◇q1))
   _=(q2◇(q0◇(q0◇(q1◇(A◇A))))):=K rfl (K rfl (S (l34 A B C D)))
   _=q0:=l4 (q2) ((A◇A)) B (q1)
 let l36:=fun (B C D:G)=>
  let q0:G:=((B◇B)◇((B◇B)◇(D◇(((B◇(B◇B))◇(B◇B))◇(B◇B)))))
  let q1:G:=(B◇(B◇(C◇(B◇B))))
  let q2:G:=((B◇(B◇B))◇(B◇B))
  have r0:(q2◇(q0◇(q1◇(q1◇(B◇B)))))=q0:=l36x B D C B
  have r1:(q2◇q1)=q0:=(K rfl (l35 B D C B)).symm.trans r0
  r1
 let l37:=fun (B C:G)=>
  let q0:G:=((B◇(B◇B))◇(B◇B))
  calc (q0◇(q0◇(B◇(B◇(C◇(B◇B))))))
   _=(q0◇((B◇B)◇((B◇B)◇(B◇(q0◇(B◇B)))))):=K rfl ((S (l36 B C B)).symm)
   _=(B◇B):=(l3 ((B◇B)) (q0) B).symm
 let l38x:=fun (A B C:G)=>
  let q0:G:=((A◇(A◇(B◇((A◇A)◇A))))◇(A◇A))
  calc (A◇A)
   _=(q0◇((A◇A)◇((A◇A)◇(C◇(q0◇(A◇A)))))):=l3 ((A◇A)) (q0) C
   _=(q0◇A):=K rfl (l24 A C B)
 let l38:=fun (B:G)=>
  have r0:(B◇B)=(((B◇(B◇(B◇((B◇B)◇B))))◇(B◇B))◇B):=l38x B B B
  have r1:(B◇B)=((B◇(B◇B))◇B):=r0.trans (K (l26 B B) rfl)
  S r1
 let l39:=fun (B:G)=>
  let q0:G:=((B◇(B◇B))◇(B◇B))
  calc q0
   _=(B◇(q0◇(q0◇(B◇(B◇q0))))):=((l3 (q0) B B).symm).symm
   _=(B◇(B◇B)):=K rfl (l37 B ((B◇(B◇B))))
 let l40:=fun (B C:G)=>
  calc ((B◇(B◇B))◇(B◇(B◇(C◇(B◇B)))))
   _=((B◇(B◇B))◇(B◇(B◇(C◇((B◇(B◇B))◇B))))):=K rfl (K rfl (K rfl (K rfl (S (l38 B)))))
   _=B:=(l3 B ((B◇(B◇B))) C).symm
 let l41:=fun (B C D E:G)=>
  let q0:G:=(B◇(B◇(C◇(((B◇(D◇(E◇B)))◇B)◇B))))
  let q1:G:=((B◇(D◇(E◇B))))
  calc (q0◇(B◇(B◇(D◇(E◇B)))))
   _=(q0◇(B◇(B◇((B◇(D◇(E◇B)))◇((B◇(D◇(E◇B)))◇B))))):=K rfl (K rfl (S (l7 B D E)))
   _=B:=l6 B C q1 q1
 let l42:=fun (B C D E F:G)=>
  have p4:∀ (x y z:G),(x◇((x◇(y◇(z◇x)))◇((x◇(y◇(z◇x)))◇x)))=(x◇(y◇(z◇x))):=by
   intro x y z
   exact l7 x y z
  have p6:∀ (x y z u w:G),((x◇(x◇(y◇((z◇x)◇x))))◇((((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇(((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇x))◇((((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇(((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇x))◇(x◇(x◇(u◇(z◇x)))))))=(((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇(((x◇(x◇(u◇(z◇x))))◇((x◇(x◇(u◇(z◇x))))◇(w◇x)))◇x)):=by
   intro x y z u w
   exact l27 x y z u w
  have p11x:∀ (A B C D E:G),((A◇(A◇(B◇(((A◇(C◇(D◇A)))◇A)◇A))))◇((((A◇(A◇(C◇(D◇A))))◇((A◇(A◇((A◇(C◇(D◇A)))◇((A◇(C◇(D◇A)))◇A))))◇(E◇A)))◇(((A◇(A◇((A◇(C◇(D◇A)))◇((A◇(C◇(D◇A)))◇A))))◇((A◇(A◇((A◇(C◇(D◇A)))◇((A◇(C◇(D◇A)))◇A))))◇(E◇A)))◇A))◇((((A◇(A◇((A◇(C◇(D◇A)))◇((A◇(C◇(D◇A)))◇A))))◇((A◇(A◇((A◇(C◇(D◇A)))◇((A◇(C◇(D◇A)))◇A))))◇(E◇A)))◇(((A◇(A◇((A◇(C◇(D◇A)))◇((A◇(C◇(D◇A)))◇A))))◇((A◇(A◇((A◇(C◇(D◇A)))◇((A◇(C◇(D◇A)))◇A))))◇(E◇A)))◇A))◇(A◇(A◇((A◇(C◇(D◇A)))◇((A◇(C◇(D◇A)))◇A)))))))=(((A◇(A◇((A◇(C◇(D◇A)))◇((A◇(C◇(D◇A)))◇A))))◇((A◇(A◇((A◇(C◇(D◇A)))◇((A◇(C◇(D◇A)))◇A))))◇(E◇A)))◇(((A◇(A◇((A◇(C◇(D◇A)))◇((A◇(C◇(D◇A)))◇A))))◇((A◇(A◇((A◇(C◇(D◇A)))◇((A◇(C◇(D◇A)))◇A))))◇(E◇A)))◇A)):=by
   intro A B C D E
   let s0:G:=(A◇(A◇((A◇(C◇(D◇A)))◇((A◇(C◇(D◇A)))◇A))))
   let s1:G:=((s0◇(s0◇(E◇A)))◇((s0◇(s0◇(E◇A)))◇A))
   let s2:G:=(A◇(A◇(B◇(((A◇(C◇(D◇A)))◇A)◇A))))
   let s3:G:=((A◇(C◇(D◇A))))
   calc (s2◇((((A◇(A◇(C◇(D◇A))))◇(s0◇(E◇A)))◇((s0◇(s0◇(E◇A)))◇A))◇(s1◇s0)))
    _=(s2◇(s1◇(s1◇s0))):=K rfl (K (K (K (K rfl (S (p4 A C D))) rfl) rfl) rfl)
    _=s1:=p6 A B s3 s3 E
  have p11:∀ (x y z u w:G),((x◇(x◇(y◇(((x◇(z◇(u◇x)))◇x)◇x))))◇((((x◇(x◇(z◇(u◇x))))◇((x◇(x◇(z◇(u◇x))))◇(w◇x)))◇(((x◇(x◇(z◇(u◇x))))◇((x◇(x◇(z◇(u◇x))))◇(w◇x)))◇x))◇((((x◇(x◇(z◇(u◇x))))◇((x◇(x◇(z◇(u◇x))))◇(w◇x)))◇(((x◇(x◇(z◇(u◇x))))◇((x◇(x◇(z◇(u◇x))))◇(w◇x)))◇x))◇(x◇(x◇(z◇(u◇x)))))))=(((x◇(x◇(z◇(u◇x))))◇((x◇(x◇(z◇(u◇x))))◇(w◇x)))◇(((x◇(x◇(z◇(u◇x))))◇((x◇(x◇(z◇(u◇x))))◇(w◇x)))◇x)):=by
   intro x y z u w
   simpa only [p4,p4,p4,p4,p4,p4,p4,p4,p4,p4,p4,p4] using (p11x x y z u w)
  p11 B C D E F
 let l43:=fun (B C:G)=>
  let q0:G:=((B◇B)◇((B◇B)◇(C◇(((B◇(B◇B))◇(B◇B))◇(B◇B)))))
  let q1:G:=(B◇(B◇(B◇(B◇B))))
  let q2:G:=((B◇(B◇B))◇(B◇B))
  have r0:(q2◇q1)=q0:=l36 B B C
  have r1:((B◇(B◇B))◇q1)=q0:=(K (l39 B) rfl).symm.trans r0
  have r2:B=q0:=(S (l40 B B)).trans r1
  have r3:B=((B◇B)◇((B◇B)◇(C◇q2))):=r2.trans (K rfl (K rfl (K rfl (K (l39 B) rfl))))
  have r4:B=((B◇B)◇((B◇B)◇(C◇(B◇(B◇B))))):=r3.trans (K rfl (K rfl (K rfl (l39 B))))
  S r4
 let l44x:=fun (A B C D E F:G)=>
  let q0:G:=((A◇(A◇(C◇(D◇A))))◇((A◇(A◇(C◇(D◇A))))◇(E◇((A◇(A◇(B◇(((A◇(C◇(D◇A)))◇A)◇A))))◇(A◇(A◇(C◇(D◇A))))))))
  let q1:G:=(A◇(A◇(B◇(((A◇(C◇(D◇A)))◇A)◇A))))
  let q2:G:=(A◇(A◇(C◇(D◇A))))
  calc (q1◇((q2◇(q2◇(E◇A)))◇(q0◇(F◇q2))))
   _=(q1◇(q0◇(q0◇(F◇q2)))):=K rfl (K (K rfl (K rfl (K rfl (S (l41 A B C D))))) rfl)
   _=q0:=l4 (q1) (q2) E F
 let l44:=fun (B C D E F X6:G)=>
  let q0:G:=(B◇(B◇(D◇(E◇B))))
  let q1:G:=(B◇(B◇(C◇(((B◇(D◇(E◇B)))◇B)◇B))))
  let q2:G:=(q1◇((q0◇(q0◇(F◇B)))◇((q0◇(q0◇(F◇B)))◇(X6◇q0))))
  let q3:G:=(q0◇(q0◇(F◇(q1◇q0))))
  have r0:(q1◇((q0◇(q0◇(F◇B)))◇(q3◇(X6◇q0))))=q3:=l44x B C D E F X6
  have r1:q2=q3:=(K rfl (K rfl (K (K rfl (K rfl (K rfl (l41 B C D E)))) rfl))).symm.trans r0
  have r2:q2=(q0◇(q0◇(F◇B))):=r1.trans (K rfl (K rfl (K rfl (l41 B C D E))))
  r2
 let l45:=fun (B C D E:G)=>
  have p5:∀ (x y:G),((x◇x)◇((x◇x)◇(y◇(x◇(x◇x)))))=x:=by
   intro x y
   exact l43 x y
  have p8:∀ (x y z u w:G),((x◇(x◇(y◇(((x◇(z◇(u◇x)))◇x)◇x))))◇((((x◇(x◇(z◇(u◇x))))◇((x◇(x◇(z◇(u◇x))))◇(w◇x)))◇(((x◇(x◇(z◇(u◇x))))◇((x◇(x◇(z◇(u◇x))))◇(w◇x)))◇x))◇((((x◇(x◇(z◇(u◇x))))◇((x◇(x◇(z◇(u◇x))))◇(w◇x)))◇(((x◇(x◇(z◇(u◇x))))◇((x◇(x◇(z◇(u◇x))))◇(w◇x)))◇x))◇(x◇(x◇(z◇(u◇x)))))))=(((x◇(x◇(z◇(u◇x))))◇((x◇(x◇(z◇(u◇x))))◇(w◇x)))◇(((x◇(x◇(z◇(u◇x))))◇((x◇(x◇(z◇(u◇x))))◇(w◇x)))◇x)):=by
   intro x y z u w
   exact l42 x y z u w
  have p6:∀ (x y z:G),(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)=(x◇x):=by
   intro x y z
   exact l22 x y z
  have p11x:∀ (A B C D:G),(((A◇A)◇((A◇A)◇(B◇((((A◇A)◇(C◇(A◇(A◇A))))◇(A◇A))◇(A◇A)))))◇(((A◇(((A◇A)◇((A◇A)◇(C◇(A◇(A◇A)))))◇(D◇(A◇A))))◇((((A◇A)◇((A◇A)◇(C◇(A◇(A◇A)))))◇(((A◇A)◇((A◇A)◇(C◇(A◇(A◇A)))))◇(D◇(A◇A))))◇(A◇A)))◇(((((A◇A)◇((A◇A)◇(C◇(A◇(A◇A)))))◇(((A◇A)◇((A◇A)◇(C◇(A◇(A◇A)))))◇(D◇(A◇A))))◇((((A◇A)◇((A◇A)◇(C◇(A◇(A◇A)))))◇(((A◇A)◇((A◇A)◇(C◇(A◇(A◇A)))))◇(D◇(A◇A))))◇(A◇A)))◇((A◇A)◇((A◇A)◇(C◇(A◇(A◇A))))))))=((((A◇A)◇((A◇A)◇(C◇(A◇(A◇A)))))◇(((A◇A)◇((A◇A)◇(C◇(A◇(A◇A)))))◇(D◇(A◇A))))◇((((A◇A)◇((A◇A)◇(C◇(A◇(A◇A)))))◇(((A◇A)◇((A◇A)◇(C◇(A◇(A◇A)))))◇(D◇(A◇A))))◇(A◇A))):=by
   intro A B C D
   let s0:G:=(((A◇A)◇((A◇A)◇(C◇(A◇(A◇A)))))◇(((A◇A)◇((A◇A)◇(C◇(A◇(A◇A)))))◇(D◇(A◇A))))
   let s1:G:=((A◇A)◇(C◇(A◇(A◇A))))
   let s2:G:=((A◇A)◇((A◇A)◇(B◇((s1◇(A◇A))◇(A◇A)))))
   let s3:G:=((s0◇(s0◇(A◇A)))◇((A◇A)◇s1))
   calc (s2◇(((A◇(((A◇A)◇s1)◇(D◇(A◇A))))◇(s0◇(A◇A)))◇s3))
    _=(s2◇((s0◇(s0◇(A◇A)))◇s3)):=K rfl (K (K (K (S (p5 A C)) rfl) rfl) rfl)
    _=(s0◇(s0◇(A◇A))):=p8 ((A◇A)) B C A D
  have p11:∀ (x y z u:G),(((x◇x)◇((x◇x)◇(y◇((((x◇x)◇(z◇(x◇(x◇x))))◇(x◇x))◇(x◇x)))))◇(((x◇(x◇(u◇(x◇x))))◇((x◇(x◇(u◇(x◇x))))◇(x◇x)))◇(x◇x)))=((x◇(x◇(u◇(x◇x))))◇((x◇(x◇(u◇(x◇x))))◇(x◇x))):=by
   intro x y z u
   let s0:G:=(((x◇x)◇((x◇x)◇(z◇(x◇(x◇x)))))◇(((x◇x)◇((x◇x)◇(z◇(x◇(x◇x)))))◇(u◇(x◇x))))
   let s1:G:=((x◇x)◇((x◇x)◇(y◇((((x◇x)◇(z◇(x◇(x◇x))))◇(x◇x))◇(x◇x)))))
   let s2:G:=((x◇(x◇(u◇(x◇x))))◇((x◇(x◇(u◇(x◇x))))◇(x◇x)))
   let s3:G:=((x◇x)◇((x◇x)◇(z◇(x◇(x◇x)))))
   let s4:G:=((x◇(x◇(u◇(x◇x))))◇((x◇(s3◇(u◇(x◇x))))◇(x◇x)))
   let s5:G:=((x◇(s3◇(u◇(x◇x))))◇(s0◇(x◇x)))
   let s6:G:=((x◇(x◇(u◇(x◇x))))◇(s0◇(x◇x)))
   let s7:G:=((s0◇(s0◇(x◇x)))◇s3)
   have r0:(s1◇(s5◇s7))=(s0◇(s0◇(x◇x))):=p11x x y z u
   have r1:(s1◇(s6◇s7))=(s0◇(s0◇(x◇x))):=(K rfl (K (K (K rfl (K (p5 x z) rfl)) rfl) rfl)).symm.trans r0
   have r2:(s1◇(s4◇s7))=(s0◇(s0◇(x◇x))):=(K rfl (K (K rfl (K (K (p5 x z) rfl) rfl)) rfl)).symm.trans r1
   have r3:(s1◇(s2◇s7))=(s0◇(s0◇(x◇x))):=(K rfl (K (K rfl (K (K rfl (K (p5 x z) rfl)) rfl)) rfl)).symm.trans r2
   have r4:(s1◇(s2◇(s5◇s3)))=(s0◇(s0◇(x◇x))):=(K rfl (K rfl (K (K (K (p5 x z) rfl) rfl) rfl))).symm.trans r3
   have r5:(s1◇(s2◇(s6◇s3)))=(s0◇(s0◇(x◇x))):=(K rfl (K rfl (K (K (K rfl (K (p5 x z) rfl)) rfl) rfl))).symm.trans r4
   have r6:(s1◇(s2◇(s4◇s3)))=(s0◇(s0◇(x◇x))):=(K rfl (K rfl (K (K rfl (K (K (p5 x z) rfl) rfl)) rfl))).symm.trans r5
   have r7:(s1◇(s2◇(s2◇s3)))=(s0◇(s0◇(x◇x))):=(K rfl (K rfl (K (K rfl (K (K rfl (K (p5 x z) rfl)) rfl)) rfl))).symm.trans r6
   have r8:(s1◇(s2◇(s2◇x)))=(s0◇(s0◇(x◇x))):=(K rfl (K rfl (K rfl (p5 x z)))).symm.trans r7
   have r9:(s1◇(s2◇(x◇x)))=(s0◇(s0◇(x◇x))):=(K rfl (K rfl (p6 x u x))).symm.trans r8
   have r10:(s1◇(s2◇(x◇x)))=s5:=r9.trans (K (K (p5 x z) rfl) rfl)
   have r11:(s1◇(s2◇(x◇x)))=s6:=r10.trans (K (K rfl (K (p5 x z) rfl)) rfl)
   have r12:(s1◇(s2◇(x◇x)))=s4:=r11.trans (K rfl (K (K (p5 x z) rfl) rfl))
   have r13:(s1◇(s2◇(x◇x)))=s2:=r12.trans (K rfl (K (K rfl (K (p5 x z) rfl)) rfl))
   exact r13
  p11 B C D E
 let l46:=fun (B C D E F:G)=>
  have p4:∀ (x y:G),((x◇x)◇((x◇x)◇(y◇((x◇(x◇x))◇(x◇x)))))=x:=by
   intro x y
   exact l28 x y
  have p6:∀ (x y z u w v5:G),((x◇(x◇(y◇(((x◇(z◇(u◇x)))◇x)◇x))))◇(((x◇(x◇(z◇(u◇x))))◇((x◇(x◇(z◇(u◇x))))◇(w◇x)))◇(((x◇(x◇(z◇(u◇x))))◇((x◇(x◇(z◇(u◇x))))◇(w◇x)))◇(v5◇(x◇(x◇(z◇(u◇x))))))))=((x◇(x◇(z◇(u◇x))))◇((x◇(x◇(z◇(u◇x))))◇(w◇x))):=by
   intro x y z u w v5
   exact l44 x y z u w v5
  have p8x:∀ (A B C D E:G),(((A◇A)◇((A◇A)◇(B◇((((A◇A)◇(C◇((A◇(A◇A))◇(A◇A))))◇(A◇A))◇(A◇A)))))◇((A◇(((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(D◇(A◇A))))◇((((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(D◇(A◇A))))◇(E◇((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))))))=(((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))◇(D◇(A◇A)))):=by
   intro A B C D E
   let s0:G:=((A◇A)◇((A◇A)◇(C◇((A◇(A◇A))◇(A◇A)))))
   let s1:G:=((A◇A)◇((A◇A)◇(B◇((((A◇A)◇(C◇((A◇(A◇A))◇(A◇A))))◇(A◇A))◇(A◇A)))))
   let s2:G:=(s0◇(s0◇(D◇(A◇A))))
   calc (s1◇((A◇(s0◇(D◇(A◇A))))◇(s2◇(E◇s0))))
    _=(s1◇(s2◇(s2◇(E◇s0)))):=K rfl (K (K (S (p4 A C)) rfl) rfl)
    _=s2:=p6 ((A◇A)) B C ((A◇(A◇A))) D E
  have p8:∀ (x y z u w:G),(((x◇x)◇((x◇x)◇(y◇((((x◇x)◇(z◇((x◇(x◇x))◇(x◇x))))◇(x◇x))◇(x◇x)))))◇((x◇(x◇(u◇(x◇x))))◇((x◇(x◇(u◇(x◇x))))◇(w◇x))))=(x◇(x◇(u◇(x◇x)))):=by
   intro x y z u w
   let s0:G:=((x◇x)◇(z◇((x◇(x◇x))◇(x◇x))))
   let s1:G:=((x◇x)◇((x◇x)◇(y◇((s0◇(x◇x))◇(x◇x)))))
   let s2:G:=(((x◇x)◇s0)◇(((x◇x)◇s0)◇(u◇(x◇x))))
   let s3:G:=(x◇(x◇(u◇(x◇x))))
   let s4:G:=(x◇(((x◇x)◇s0)◇(u◇(x◇x))))
   let s5:G:=(s1◇(s3◇(s3◇(w◇x))))
   let s6:G:=(s2◇(w◇((x◇x)◇s0)))
   have r0:(s1◇(s4◇s6))=s2:=p8x x y z u w
   have r1:(s1◇(s3◇s6))=s2:=(K rfl (K (K rfl (K (p4 x z) rfl)) rfl)).symm.trans r0
   have r2:(s1◇(s3◇(s4◇(w◇((x◇x)◇s0)))))=s2:=(K rfl (K rfl (K (K (p4 x z) rfl) rfl))).symm.trans r1
   have r3:(s1◇(s3◇(s3◇(w◇((x◇x)◇s0)))))=s2:=(K rfl (K rfl (K (K rfl (K (p4 x z) rfl)) rfl))).symm.trans r2
   have r4:s5=s2:=(K rfl (K rfl (K rfl (K rfl (p4 x z))))).symm.trans r3
   have r5:s5=s4:=r4.trans (K (p4 x z) rfl)
   have r6:s5=s3:=r5.trans (K rfl (K (p4 x z) rfl))
   exact r6
  p8 B C D E F
 let l47:=fun (B C D E F:G)=>
  let q0:G:=(B◇(B◇(E◇(B◇B))))
  let q1:G:=((B◇B)◇((B◇B)◇(C◇((((B◇B)◇(D◇(B◇(B◇B))))◇(B◇B))◇(B◇B)))))
  calc (q1◇((q0◇(q0◇(F◇B)))◇(B◇B)))
   _=(q1◇((q0◇(q0◇(B◇B)))◇(B◇B))):=K rfl (K (l32 B E F B) rfl)
   _=(q0◇(q0◇(B◇B))):=l45 B C D E
   _=(q0◇(q0◇(F◇B))):=S (l32 B E F B)
 let l48:=fun (B C D E F:G)=>
  let q0:G:=(B◇(B◇(E◇(B◇B))))
  calc (((B◇B)◇((B◇B)◇(C◇((((B◇B)◇(D◇(B◇(B◇B))))◇(B◇B))◇(B◇B)))))◇(q0◇(q0◇(F◇B))))
   _=(((B◇B)◇((B◇B)◇(C◇((((B◇B)◇(D◇((B◇(B◇B))◇(B◇B))))◇(B◇B))◇(B◇B)))))◇(q0◇(q0◇(F◇B)))):=K (K rfl (K rfl (K rfl (K (K (K rfl (K rfl (S (l39 B)))) rfl) rfl)))) rfl
   _=q0:=l46 B C D E F
 let l49x:=fun (A B C D E:G)=>
  let q0:G:=((A◇A)◇((A◇A)◇(C◇((((A◇A)◇(B◇(A◇(A◇A))))◇(A◇A))◇(A◇A)))))
  let q1:G:=((A◇(A◇(D◇(A◇A))))◇((A◇(A◇(D◇(A◇A))))◇(E◇A)))
  let q2:G:=(((A◇A)◇(B◇(A◇(A◇A))))◇(A◇A))
  calc (q2◇(q0◇q1))
   _=(q2◇(q0◇(q0◇(q1◇(A◇A))))):=K rfl (K rfl (S (l47 A C B D E)))
   _=q0:=l4 (q2) ((A◇A)) C (q1)
 let l49:=fun (B C D E:G)=>
  let q0:G:=((B◇B)◇((B◇B)◇(E◇((((B◇B)◇(C◇(B◇(B◇B))))◇(B◇B))◇(B◇B)))))
  let q1:G:=(B◇(B◇(D◇(B◇B))))
  let q2:G:=(((B◇B)◇(C◇(B◇(B◇B))))◇(B◇B))
  have r0:(q2◇(q0◇(q1◇(q1◇(B◇B)))))=q0:=l49x B C E D B
  have r1:(q2◇q1)=q0:=(K rfl (l48 B E C D B)).symm.trans r0
  r1
 let l50x:=fun (A B C D E:G)=>
  let q0:G:=((A◇(A◇(B◇((C◇A)◇A))))◇(C◇A))
  let q1:G:=(A◇(A◇(B◇((C◇A)◇A))))
  let q2:G:=(q0◇(q0◇(D◇((((C◇A)◇((C◇A)◇(E◇(q0◇(C◇A)))))◇q0)◇q0))))
  calc (q2◇((C◇A)◇q1))
   _=(q2◇((C◇A)◇((C◇A)◇(q1◇q0)))):=K rfl (K rfl ((l4 ((C◇A)) A B C).symm))
   _=(C◇A):=l10 (q1) ((C◇A)) D E (q1)
 let l50:=fun (B C D E F:G)=>
  let q0:G:=((B◇(B◇(C◇((D◇B)◇B))))◇(D◇B))
  let q1:G:=(q0◇(q0◇(E◇((((D◇B)◇((D◇B)◇(F◇(q0◇(D◇B)))))◇q0)◇q0))))
  have r0:(q1◇((D◇B)◇(B◇(B◇(C◇((D◇B)◇B))))))=(D◇B):=l50x B C D E F
  have r1:(q1◇B)=(D◇B):=(K rfl ((l3 B (D◇B) C).symm)).symm.trans r0
  r1
 let l51:=fun (B C D:G)=>
  let q0:G:=(((B◇B)◇(C◇(B◇(B◇B))))◇(B◇B))
  calc (q0◇(q0◇(B◇(B◇(D◇(B◇B))))))
   _=(q0◇((B◇B)◇((B◇B)◇(B◇(q0◇(B◇B)))))):=K rfl ((S (l49 B C D B)).symm)
   _=(B◇B):=(l3 ((B◇B)) (q0) B).symm
 let l52:=fun (B C D E F X6:G)=>
  let q0:G:=(((B◇(B◇(C◇((D◇B)◇B))))◇(D◇B))◇(((B◇(B◇(C◇((D◇B)◇B))))◇(D◇B))◇(E◇((((D◇B)◇((D◇B)◇(F◇(((B◇(B◇(C◇((D◇B)◇B))))◇(D◇B))◇(D◇B)))))◇((B◇(B◇(C◇((D◇B)◇B))))◇(D◇B)))◇((B◇(B◇(C◇((D◇B)◇B))))◇(D◇B))))))
  calc (q0◇(B◇(B◇(X6◇(D◇B)))))
   _=(q0◇(B◇(B◇(X6◇(q0◇B))))):=K rfl (K rfl (K rfl (K rfl (S (l50 B C D E F)))))
   _=B:=(l3 B (q0) X6).symm
 let l53x:=fun (A B C D:G)=>
  let q0:G:=(A◇(A◇(B◇(C◇A))))
  let q1:G:=((q0◇(D◇(C◇q0)))◇q0)
  calc (q0◇((q0◇(D◇A))◇q1))
   _=(q0◇((q0◇(D◇(C◇q0)))◇q1)):=K rfl (K (K rfl (K rfl ((S (l3 A C B)).symm))) rfl)
   _=(q0◇(D◇(C◇q0))):=l7 (q0) D C
 let l53:=fun (B C D E:G)=>
  let q0:G:=(B◇(B◇(C◇(D◇B))))
  let q1:G:=(q0◇((q0◇(E◇B))◇((q0◇(E◇B))◇q0)))
  have r0:(q0◇((q0◇(E◇B))◇((q0◇(E◇(D◇q0)))◇q0)))=(q0◇(E◇(D◇q0))):=l53x B C D E
  have r1:q1=(q0◇(E◇(D◇q0))):=(K rfl (K rfl (K (K rfl (K rfl (S (l3 B D C)))) rfl))).symm.trans r0
  have r2:q1=(q0◇(E◇B)):=r1.trans (K rfl (K rfl (S (l3 B D C))))
  r2
 let l54:=fun (B C:G)=>
  let q0:G:=(((B◇B)◇(C◇(B◇(B◇B))))◇(B◇B))
  calc q0
   _=(B◇(q0◇(q0◇(B◇(B◇q0))))):=((l3 (q0) B B).symm).symm
   _=(B◇(B◇B)):=K rfl (l51 B C (((B◇B)◇(C◇(B◇(B◇B))))))
 let l55:=fun (B C D E:G)=>
  have p4:∀ (x y:G),((x◇x)◇((x◇x)◇(y◇((x◇(x◇x))◇(x◇x)))))=x:=by
   intro x y
   exact l28 x y
  have p5:∀ (x y z u w v5:G),((((x◇(x◇(y◇((z◇x)◇x))))◇(z◇x))◇(((x◇(x◇(y◇((z◇x)◇x))))◇(z◇x))◇(u◇((((z◇x)◇((z◇x)◇(w◇(((x◇(x◇(y◇((z◇x)◇x))))◇(z◇x))◇(z◇x)))))◇((x◇(x◇(y◇((z◇x)◇x))))◇(z◇x)))◇((x◇(x◇(y◇((z◇x)◇x))))◇(z◇x))))))◇(x◇(x◇(v5◇(z◇x)))))=x:=by
   intro x y z u w v5
   exact l52 x y z u w v5
  have p7x:∀ (A B C D E:G),(((A◇(A◇(A◇A)))◇((((A◇A)◇((A◇A)◇(B◇((A◇(A◇A))◇(A◇A)))))◇(A◇(A◇A)))◇(C◇((((A◇(A◇A))◇((A◇(A◇A))◇(D◇((((A◇A)◇((A◇A)◇(B◇((A◇(A◇A))◇(A◇A)))))◇(A◇(A◇A)))◇(A◇(A◇A))))))◇(((A◇A)◇((A◇A)◇(B◇((A◇(A◇A))◇(A◇A)))))◇(A◇(A◇A))))◇(((A◇A)◇((A◇A)◇(B◇((A◇(A◇A))◇(A◇A)))))◇(A◇(A◇A)))))))◇((A◇A)◇((A◇A)◇(E◇(A◇(A◇A))))))=(A◇A):=by
   intro A B C D E
   let s0:G:=(((A◇A)◇((A◇A)◇(B◇((A◇(A◇A))◇(A◇A)))))◇(A◇(A◇A)))
   let s1:G:=(s0◇(C◇((((A◇(A◇A))◇((A◇(A◇A))◇(D◇(s0◇(A◇(A◇A))))))◇s0)◇s0)))
   let s2:G:=((A◇A)◇((A◇A)◇(E◇(A◇(A◇A)))))
   calc (((A◇(A◇(A◇A)))◇s1)◇s2)
    _=((s0◇s1)◇s2):=K (K (K (S (p4 A B)) rfl) rfl) rfl
    _=(A◇A):=p5 ((A◇A)) B A C D E
  have p7:∀ (x y z u:G),(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇((((x◇(x◇x))◇((x◇(x◇x))◇(z◇((x◇(x◇(x◇x)))◇(x◇(x◇x))))))◇(x◇(x◇(x◇x))))◇(x◇(x◇(x◇x)))))))◇((x◇x)◇((x◇x)◇(u◇(x◇(x◇x))))))=(x◇x):=by
   intro x y z u
   let s0:G:=(((x◇x)◇((x◇x)◇(x◇((x◇(x◇x))◇(x◇x)))))◇(x◇(x◇x)))
   let s1:G:=((x◇x)◇((x◇x)◇(u◇(x◇(x◇x)))))
   let s2:G:=((x◇(x◇x))◇((x◇(x◇x))◇(z◇((x◇(x◇(x◇x)))◇(x◇(x◇x))))))
   let s3:G:=(y◇((((x◇(x◇x))◇((x◇(x◇x))◇(z◇(s0◇(x◇(x◇x))))))◇s0)◇s0))
   let s4:G:=(s2◇(x◇(x◇(x◇x))))
   have r0:(((x◇(x◇(x◇x)))◇(s0◇s3))◇s1)=(x◇x):=p7x x x y z u
   have r1:(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇s3))◇s1)=(x◇x):=(K (K rfl (K (K (p4 x x) rfl) rfl)) rfl).symm.trans r0
   have r2:(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇((s2◇s0)◇s0))))◇s1)=(x◇x):=(K (K rfl (K rfl (K rfl (K (K (K rfl (K rfl (K rfl (K (K (p4 x x) rfl) rfl)))) rfl) rfl)))) rfl).symm.trans r1
   have r3:(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇(s4◇s0))))◇s1)=(x◇x):=(K (K rfl (K rfl (K rfl (K (K rfl (K (p4 x x) rfl)) rfl)))) rfl).symm.trans r2
   have r4:(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇(s4◇(x◇(x◇(x◇x)))))))◇s1)=(x◇x):=(K (K rfl (K rfl (K rfl (K rfl (K (p4 x x) rfl))))) rfl).symm.trans r3
   exact r4
  p7 B C D E
 let l56:=fun (B C:G)=>
  let q0:G:=(B◇(B◇(C◇((B◇B)◇B))))
  calc ((B◇B)◇(q0◇(B◇(B◇B))))
   _=((B◇B)◇(q0◇(q0◇(B◇B)))):=K rfl (K rfl (S (l26 B C)))
   _=q0:=l4 ((B◇B)) B C B
 let l57:=fun (B C D E F:G)=>
  let q0:G:=(((B◇(B◇(C◇(D◇B))))◇(E◇B))◇(B◇(B◇(C◇(D◇B)))))
  let q1:G:=((B◇(B◇(C◇(D◇B))))◇(E◇B))
  let q2:G:=(q0◇(q0◇(F◇((q1◇q0)◇q0))))
  let q3:G:=(B◇(B◇(C◇(D◇B))))
  calc (q2◇(q0◇(q0◇q1)))
   _=(q2◇(q0◇(q0◇(q3◇(q1◇q0))))):=K rfl (K rfl (K rfl (S (l53 B C D E))))
   _=q0:=l6 (q0) F (q1) (q3)
 let l58:=fun (B C D:G)=>
  have p7:∀ (x y z u w:G),(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇((x◇(x◇(u◇(x◇x))))◇((x◇(x◇(u◇(x◇x))))◇(w◇x))))=(x◇(x◇(u◇(x◇x)))):=by
   intro x y z u w
   exact l29 x y z u w
  have p5:∀ (x y:G),(((x◇x)◇(y◇(x◇(x◇x))))◇(x◇x))=(x◇(x◇x)):=by
   intro x y
   exact l54 x y
  have p6:∀ (x y z u:G),(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(x◇(x◇(u◇(x◇x)))))=x:=by
   intro x y z u
   exact l30 x y z u
  have p10x:∀ (A B C D:G),(((A◇(A◇(B◇(A◇A))))◇(C◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(D◇A)))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(D◇A)))◇((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(D◇A)))))))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(D◇A)))◇((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(D◇A)))))=(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(D◇A)))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(D◇A)))◇((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(D◇A))))):=by
   intro A B C D
   let s0:G:=((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(D◇A)))
   calc (((A◇(A◇(B◇(A◇A))))◇(C◇(s0◇(s0◇s0))))◇(s0◇s0))
    _=(((s0◇s0)◇(C◇(s0◇(s0◇s0))))◇(s0◇s0)):=K (K (S (p7 A B D B D)) rfl) rfl
    _=(s0◇(s0◇s0)):=p5 (s0) C
  have p10:∀ (x y z:G),(((x◇(x◇(y◇(x◇x))))◇(z◇x))◇(x◇(x◇(y◇(x◇x)))))=x:=by
   intro x y z
   let s0:G:=((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(x◇x)))
   let s1:G:=(x◇(x◇(y◇(x◇x))))
   have r0:((s1◇(z◇(s0◇(s0◇s0))))◇(s0◇s0))=(s0◇(s0◇s0)):=p10x x y z x
   have r1:((s1◇(z◇(s0◇s1)))◇(s0◇s0))=(s0◇(s0◇s0)):=(K (K rfl (K rfl (K rfl (p7 x y x y x)))) rfl).symm.trans r0
   have r2:((s1◇(z◇x))◇(s0◇s0))=(s0◇(s0◇s0)):=(K (K rfl (K rfl (p6 x y x y))) rfl).symm.trans r1
   have r3:((s1◇(z◇x))◇s1)=(s0◇(s0◇s0)):=(K rfl (p7 x y x y x)).symm.trans r2
   have r4:((s1◇(z◇x))◇s1)=(s0◇s1):=r3.trans (K rfl (p7 x y x y x))
   have r5:((s1◇(z◇x))◇s1)=x:=r4.trans (p6 x y x y)
   exact r5
  p10 B C D
 let l59x:=fun (A B C D:G)=>
  let q0:G:=((A◇(A◇(A◇A)))◇((A◇(A◇(A◇A)))◇(B◇((((A◇(A◇A))◇((A◇(A◇A))◇(C◇((A◇(A◇(A◇A)))◇(A◇(A◇A))))))◇(A◇(A◇(A◇A))))◇(A◇(A◇(A◇A)))))))
  let q1:G:=(A◇(A◇(D◇((A◇A)◇A))))
  calc (q0◇((A◇A)◇q1))
   _=(q0◇((A◇A)◇((A◇A)◇(q1◇(A◇(A◇A)))))):=K rfl (K rfl (S (l56 A D)))
   _=(A◇A):=l55 A B C (q1)
 let l59:=fun (B C D:G)=>
  let q0:G:=((B◇(B◇(B◇B)))◇((B◇(B◇(B◇B)))◇(C◇((((B◇(B◇B))◇((B◇(B◇B))◇(D◇((B◇(B◇(B◇B)))◇(B◇(B◇B))))))◇(B◇(B◇(B◇B))))◇(B◇(B◇(B◇B)))))))
  have r0:(q0◇((B◇B)◇(B◇(B◇(B◇((B◇B)◇B))))))=(B◇B):=l59x B C D B
  have r1:(q0◇B)=(B◇B):=(K rfl ((l3 B (B◇B) B).symm)).symm.trans r0
  r1
 let l60:=fun (B C D E:G)=>
  have p4:∀ (x y z:G),(((x◇(x◇(y◇(x◇x))))◇(z◇x))◇(x◇(x◇(y◇(x◇x)))))=x:=by
   intro x y z
   exact l58 x y z
  have p5:∀ (x y z u w:G),(((((x◇(x◇(y◇(z◇x))))◇(u◇x))◇(x◇(x◇(y◇(z◇x)))))◇((((x◇(x◇(y◇(z◇x))))◇(u◇x))◇(x◇(x◇(y◇(z◇x)))))◇(w◇((((x◇(x◇(y◇(z◇x))))◇(u◇x))◇(((x◇(x◇(y◇(z◇x))))◇(u◇x))◇(x◇(x◇(y◇(z◇x))))))◇(((x◇(x◇(y◇(z◇x))))◇(u◇x))◇(x◇(x◇(y◇(z◇x)))))))))◇((((x◇(x◇(y◇(z◇x))))◇(u◇x))◇(x◇(x◇(y◇(z◇x)))))◇((((x◇(x◇(y◇(z◇x))))◇(u◇x))◇(x◇(x◇(y◇(z◇x)))))◇((x◇(x◇(y◇(z◇x))))◇(u◇x)))))=(((x◇(x◇(y◇(z◇x))))◇(u◇x))◇(x◇(x◇(y◇(z◇x))))):=by
   intro x y z u w
   exact l57 x y z u w
  have p8x:∀ (A B C D:G),((A◇((((A◇(A◇(B◇(A◇A))))◇(C◇A))◇(A◇(A◇(B◇(A◇A)))))◇(D◇((((A◇(A◇(B◇(A◇A))))◇(C◇A))◇(((A◇(A◇(B◇(A◇A))))◇(C◇A))◇(A◇(A◇(B◇(A◇A))))))◇(((A◇(A◇(B◇(A◇A))))◇(C◇A))◇(A◇(A◇(B◇(A◇A)))))))))◇((((A◇(A◇(B◇(A◇A))))◇(C◇A))◇(A◇(A◇(B◇(A◇A)))))◇((((A◇(A◇(B◇(A◇A))))◇(C◇A))◇(A◇(A◇(B◇(A◇A)))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))))=(((A◇(A◇(B◇(A◇A))))◇(C◇A))◇(A◇(A◇(B◇(A◇A))))):=by
   intro A B C D
   let s0:G:=(((A◇(A◇(B◇(A◇A))))◇(C◇A))◇(A◇(A◇(B◇(A◇A)))))
   let s1:G:=((A◇(A◇(B◇(A◇A))))◇(C◇A))
   let s2:G:=(s0◇(D◇((s1◇s0)◇s0)))
   calc ((A◇s2)◇(s0◇(s0◇s1)))
    _=((s0◇s2)◇(s0◇(s0◇s1))):=K (K (S (p4 A B C)) rfl) rfl
    _=s0:=p5 A B A C D
  have p8:∀ (x y z u:G),((x◇(x◇(y◇((((x◇(x◇(z◇(x◇x))))◇(u◇x))◇x)◇x))))◇(x◇(x◇((x◇(x◇(z◇(x◇x))))◇(u◇x)))))=x:=by
   intro x y z u
   let s0:G:=(((x◇(x◇(z◇(x◇x))))◇(u◇x))◇(x◇(x◇(z◇(x◇x)))))
   let s1:G:=((x◇(x◇(z◇(x◇x))))◇(u◇x))
   let s2:G:=(x◇(x◇(y◇((s1◇x)◇x))))
   have r0:((x◇(s0◇(y◇((s1◇s0)◇s0))))◇(s0◇(s0◇s1)))=s0:=p8x x z u y
   have r1:((x◇(x◇(y◇((s1◇s0)◇s0))))◇(s0◇(s0◇s1)))=s0:=(K (K rfl (K (p4 x z u) rfl)) rfl).symm.trans r0
   have r2:((x◇(x◇(y◇((s1◇x)◇s0))))◇(s0◇(s0◇s1)))=s0:=(K (K rfl (K rfl (K rfl (K (K rfl (p4 x z u)) rfl)))) rfl).symm.trans r1
   have r3:(s2◇(s0◇(s0◇s1)))=s0:=(K (K rfl (K rfl (K rfl (K rfl (p4 x z u))))) rfl).symm.trans r2
   have r4:(s2◇(x◇(s0◇s1)))=s0:=(K rfl (K (p4 x z u) rfl)).symm.trans r3
   have r5:(s2◇(x◇(x◇s1)))=s0:=(K rfl (K rfl (K (p4 x z u) rfl))).symm.trans r4
   have r6:(s2◇(x◇(x◇s1)))=x:=r5.trans (p4 x z u)
   exact r6
  p8 B C D E
 let l61:=fun (B C D E:G)=>
  let q0:G:=((B◇(B◇(B◇B)))◇((B◇(B◇(B◇B)))◇(C◇((((B◇(B◇B))◇((B◇(B◇B))◇(D◇((B◇(B◇(B◇B)))◇(B◇(B◇B))))))◇(B◇(B◇(B◇B))))◇(B◇(B◇(B◇B)))))))
  calc (q0◇(B◇(B◇(E◇(B◇B)))))
   _=(q0◇(B◇(B◇(E◇(q0◇B))))):=K rfl (K rfl (K rfl (K rfl (S (l59 B C D)))))
   _=B:=(l3 B (q0) E).symm
 let l62:=fun (B C D:G)=>
  let q0:G:=((B◇B)◇((B◇B)◇(D◇((B◇B)◇(B◇B)))))
  let q1:G:=((B◇B)◇((B◇B)◇(C◇(((q0◇(B◇(B◇B)))◇(B◇B))◇(B◇B)))))
  calc (q1◇B)
   _=(q1◇((B◇B)◇((B◇B)◇(q0◇(B◇(B◇B)))))):=K rfl ((l43 B (q0)).symm)
   _=(B◇B):=l60 ((B◇B)) C D B
 let l63:=fun (B C D E:G)=>
  let q0:G:=(B◇(B◇(C◇(B◇B))))
  calc ((q0◇(q0◇(D◇B)))◇(q0◇(q0◇(E◇B))))
   _=((q0◇(q0◇(D◇B)))◇(q0◇(q0◇(E◇((q0◇(q0◇(D◇B)))◇q0))))):=K rfl (K rfl (K rfl (K rfl (S (l20 B C D)))))
   _=q0:=(l3 (q0) ((q0◇(q0◇(D◇B)))) E).symm
 let l64x:=fun (A B C:G)=>
  let q0:G:=((A◇(A◇(A◇A)))◇((A◇(A◇(A◇A)))◇(B◇((((A◇(A◇A))◇((A◇(A◇A))◇(C◇((A◇(A◇(A◇A)))◇(A◇(A◇A))))))◇(A◇(A◇(A◇A))))◇(A◇(A◇(A◇A)))))))
  let q1:G:=(q0◇(A◇(A◇(A◇(A◇A)))))
  calc (q1◇(q0◇A))
   _=(q1◇(q0◇q1)):=K rfl (K rfl (S (l61 A B C A)))
   _=q0:=l17 ((A◇(A◇(A◇A)))) B ((((A◇(A◇A))◇((A◇(A◇A))◇(C◇((A◇(A◇(A◇A)))◇(A◇(A◇A))))))◇(A◇(A◇(A◇A))))) A
 let l64:=fun (B C D:G)=>
  let q0:G:=((B◇(B◇(B◇B)))◇((B◇(B◇(B◇B)))◇(C◇((((B◇(B◇B))◇((B◇(B◇B))◇(D◇((B◇(B◇(B◇B)))◇(B◇(B◇B))))))◇(B◇(B◇(B◇B))))◇(B◇(B◇(B◇B)))))))
  let q1:G:=(q0◇(B◇(B◇(B◇(B◇B)))))
  have r0:(q1◇(q0◇B))=q0:=l64x B C D
  have r1:(q1◇(B◇B))=q0:=(K rfl (l59 B C D)).symm.trans r0
  have r2:(B◇(B◇B))=q0:=(K (l61 B C D B) rfl).symm.trans r1
  S r2
 let l65:=fun (B C D E F:G)=>
  have p6:∀ (x y z:G),(((x◇x)◇((x◇x)◇(y◇(((((x◇x)◇((x◇x)◇(z◇((x◇x)◇(x◇x)))))◇(x◇(x◇x)))◇(x◇x))◇(x◇x)))))◇x)=(x◇x):=by
   intro x y z
   exact l62 x y z
  have p8:∀ (x y z u:G),(x◇(((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y)))◇(((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y)))◇y)))=((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y))):=by
   intro x y z u
   exact l14 x y z u
  have p5:∀ (x y z:G),(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)=(x◇x):=by
   intro x y z
   exact l22 x y z
  have p12x:∀ (A B C D E:G),(((A◇A)◇((A◇A)◇(B◇(((((A◇A)◇((A◇A)◇(C◇((A◇A)◇(A◇A)))))◇(A◇(A◇A)))◇(A◇A))◇(A◇A)))))◇(((A◇(A◇(D◇(A◇A))))◇((A◇(A◇(D◇(((A◇A)◇((A◇A)◇(B◇(((((A◇A)◇((A◇A)◇(C◇((A◇A)◇(A◇A)))))◇(A◇(A◇A)))◇(A◇A))◇(A◇A)))))◇A))))◇(E◇A)))◇(((A◇(A◇(D◇(((A◇A)◇((A◇A)◇(B◇(((((A◇A)◇((A◇A)◇(C◇((A◇A)◇(A◇A)))))◇(A◇(A◇A)))◇(A◇A))◇(A◇A)))))◇A))))◇((A◇(A◇(D◇(((A◇A)◇((A◇A)◇(B◇(((((A◇A)◇((A◇A)◇(C◇((A◇A)◇(A◇A)))))◇(A◇(A◇A)))◇(A◇A))◇(A◇A)))))◇A))))◇(E◇A)))◇A)))=((A◇(A◇(D◇(((A◇A)◇((A◇A)◇(B◇(((((A◇A)◇((A◇A)◇(C◇((A◇A)◇(A◇A)))))◇(A◇(A◇A)))◇(A◇A))◇(A◇A)))))◇A))))◇((A◇(A◇(D◇(((A◇A)◇((A◇A)◇(B◇(((((A◇A)◇((A◇A)◇(C◇((A◇A)◇(A◇A)))))◇(A◇(A◇A)))◇(A◇A))◇(A◇A)))))◇A))))◇(E◇A))):=by
   intro A B C D E
   let s0:G:=((A◇A)◇((A◇A)◇(B◇(((((A◇A)◇((A◇A)◇(C◇((A◇A)◇(A◇A)))))◇(A◇(A◇A)))◇(A◇A))◇(A◇A)))))
   let s1:G:=((A◇(A◇(D◇(s0◇A))))◇((A◇(A◇(D◇(s0◇A))))◇(E◇A)))
   calc (s0◇(((A◇(A◇(D◇(A◇A))))◇((A◇(A◇(D◇(s0◇A))))◇(E◇A)))◇(s1◇A)))
    _=(s0◇(s1◇(s1◇A))):=K rfl (K (K (K rfl (K rfl (K rfl (S (p6 A B C))))) rfl) rfl)
    _=s1:=p8 (s0) A D E
  have p12:∀ (x y z u w:G),(((x◇x)◇((x◇x)◇(y◇(((((x◇x)◇((x◇x)◇(z◇((x◇x)◇(x◇x)))))◇(x◇(x◇x)))◇(x◇x))◇(x◇x)))))◇(((x◇(x◇(u◇(x◇x))))◇((x◇(x◇(u◇(x◇x))))◇(w◇x)))◇(x◇x)))=((x◇(x◇(u◇(x◇x))))◇((x◇(x◇(u◇(x◇x))))◇(w◇x))):=by
   intro x y z u w
   let s0:G:=((x◇x)◇((x◇x)◇(y◇(((((x◇x)◇((x◇x)◇(z◇((x◇x)◇(x◇x)))))◇(x◇(x◇x)))◇(x◇x))◇(x◇x)))))
   let s1:G:=((x◇(x◇(u◇(x◇x))))◇((x◇(x◇(u◇(x◇x))))◇(w◇x)))
   let s2:G:=((x◇(x◇(u◇(s0◇x))))◇((x◇(x◇(u◇(s0◇x))))◇(w◇x)))
   let s3:G:=((x◇(x◇(u◇(x◇x))))◇((x◇(x◇(u◇(s0◇x))))◇(w◇x)))
   have r0:(s0◇(s3◇(s2◇x)))=s2:=p12x x y z u w
   have r1:(s0◇(s1◇(s2◇x)))=s2:=(K rfl (K (K rfl (K (K rfl (K rfl (K rfl (p6 x y z)))) rfl)) rfl)).symm.trans r0
   have r2:(s0◇(s1◇(s3◇x)))=s2:=(K rfl (K rfl (K (K (K rfl (K rfl (K rfl (p6 x y z)))) rfl) rfl))).symm.trans r1
   have r3:(s0◇(s1◇(s1◇x)))=s2:=(K rfl (K rfl (K (K rfl (K (K rfl (K rfl (K rfl (p6 x y z)))) rfl)) rfl))).symm.trans r2
   have r4:(s0◇(s1◇(x◇x)))=s2:=(K rfl (K rfl (p5 x u w))).symm.trans r3
   have r5:(s0◇(s1◇(x◇x)))=s3:=r4.trans (K (K rfl (K rfl (K rfl (p6 x y z)))) rfl)
   have r6:(s0◇(s1◇(x◇x)))=s1:=r5.trans (K rfl (K (K rfl (K rfl (K rfl (p6 x y z)))) rfl))
   exact r6
  p12 B C D E F
 let l66x:=fun (A B C D E:G)=>
  let q0:G:=((A◇A)◇((A◇A)◇(B◇(((((A◇A)◇((A◇A)◇(C◇((A◇A)◇(A◇A)))))◇(A◇(A◇A)))◇(A◇A))◇(A◇A)))))
  let q1:G:=(A◇(A◇(D◇(q0◇A))))
  calc (q0◇((A◇(A◇(D◇(A◇A))))◇(q1◇(E◇A))))
   _=(q0◇(q1◇(q1◇(E◇A)))):=K rfl (K (K rfl (K rfl (K rfl (S (l62 A B C))))) rfl)
   _=q1:=l4 (q0) A D E
 let l66:=fun (B C D E F:G)=>
  let q0:G:=((B◇B)◇((B◇B)◇(C◇(((((B◇B)◇((B◇B)◇(D◇((B◇B)◇(B◇B)))))◇(B◇(B◇B)))◇(B◇B))◇(B◇B)))))
  let q1:G:=(B◇(B◇(E◇(B◇B))))
  let q2:G:=(B◇(B◇(E◇(q0◇B))))
  let q3:G:=(q0◇(q1◇(q1◇(F◇B))))
  have r0:(q0◇(q1◇(q2◇(F◇B))))=q2:=l66x B C D E F
  have r1:q3=q2:=(K rfl (K rfl (K (K rfl (K rfl (K rfl (l62 B C D)))) rfl))).symm.trans r0
  have r2:q3=q1:=r1.trans (K rfl (K rfl (K rfl (l62 B C D))))
  r2
 let l67x:=fun (A B C D E:G)=>
  let q0:G:=((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))
  let q1:G:=(q0◇(q0◇(D◇(q0◇q0))))
  calc (((q0◇(q0◇(D◇(A◇(A◇(B◇(A◇A)))))))◇(q1◇(E◇q0)))◇q1)
   _=((q1◇(q1◇(E◇q0)))◇q1):=K (K (K rfl (K rfl (K rfl (S (l63 A B C C))))) rfl) rfl
   _=q0:=l20 (q0) D E
 let l67:=fun (B C D E F:G)=>
  let q0:G:=((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))
  let q1:G:=(q0◇(q0◇(E◇(B◇(B◇(C◇(B◇B)))))))
  let q2:G:=(q0◇(q0◇(E◇(q0◇q0))))
  have r0:((q1◇(q2◇(F◇q0)))◇q2)=q0:=l67x B C D E F
  have r1:((q1◇(q1◇(F◇q0)))◇q2)=q0:=(K (K rfl (K (K rfl (K rfl (K rfl (l63 B C D D)))) rfl)) rfl).symm.trans r0
  have r2:((q1◇(q1◇(F◇q0)))◇q1)=q0:=(K rfl (K rfl (K rfl (K rfl (l63 B C D D))))).symm.trans r1
  r2
 let l68:=fun (B C D E:G)=>
  let q0:G:=((B◇B)◇((B◇B)◇(C◇(((((B◇B)◇((B◇B)◇(D◇((B◇B)◇(B◇B)))))◇(B◇(B◇B)))◇(B◇B))◇(B◇B)))))
  calc (q0◇(B◇(B◇(E◇(B◇B)))))
   _=(q0◇(B◇(B◇(E◇(q0◇B))))):=K rfl (K rfl (K rfl (K rfl (S (l62 B C D)))))
   _=B:=(l3 B (q0) E).symm
 let l69:=fun (B:G)=>
  calc ((B◇(B◇B))◇(B◇(B◇B)))
   _=(((B◇(B◇(B◇B)))◇((B◇(B◇(B◇B)))◇(B◇((((B◇(B◇B))◇((B◇(B◇B))◇(B◇((B◇(B◇(B◇B)))◇(B◇(B◇B))))))◇(B◇(B◇(B◇B))))◇(B◇(B◇(B◇B)))))))◇(B◇(B◇B))):=K (S (l64 B B B)) rfl
   _=(B◇(B◇(B◇B))):=l8 B ((B◇(B◇B))) B B
 let l70x:=fun (A B C D:G)=>
  let q0:G:=((A◇(A◇(B◇(C◇A))))◇(D◇A))
  let q1:G:=(A◇(A◇(B◇(C◇A))))
  let q2:G:=(q0◇(q0◇(C◇(q1◇q0))))
  calc ((q0◇q1)◇q2)
   _=((q0◇(C◇(q1◇q0)))◇q2):=K (K rfl (S (l4 C A B D))) rfl
   _=q0:=l9 (q0) C (q1)
 let l70:=fun (B C D E:G)=>
  let q0:G:=((B◇(B◇(C◇(D◇B))))◇(E◇B))
  let q1:G:=(B◇(B◇(C◇(D◇B))))
  have r0:((q0◇q1)◇(q0◇(q0◇(D◇(q1◇q0)))))=q0:=l70x B C D E
  have r1:((q0◇q1)◇(q0◇(q0◇q1)))=q0:=(K rfl (K rfl (K rfl (l4 D B C E)))).symm.trans r0
  r1
 let l71:=fun (B C D:G)=>
  have p9:∀ (x y z u w:G),(((x◇x)◇((x◇x)◇(y◇(((((x◇x)◇((x◇x)◇(z◇((x◇x)◇(x◇x)))))◇(x◇(x◇x)))◇(x◇x))◇(x◇x)))))◇(((x◇(x◇(u◇(x◇x))))◇((x◇(x◇(u◇(x◇x))))◇(w◇x)))◇(x◇x)))=((x◇(x◇(u◇(x◇x))))◇((x◇(x◇(u◇(x◇x))))◇(w◇x))):=by
   intro x y z u w
   exact l65 x y z u w
  have p7:∀ (x y z u:G),(((x◇(x◇(y◇(z◇x))))◇(u◇x))◇((x◇(x◇(y◇(z◇x))))◇((x◇(x◇(y◇(z◇x))))◇(u◇x))))=(x◇(x◇(y◇(z◇x)))):=by
   intro x y z u
   exact l17 x y z u
  have p8:∀ (x y z u w:G),(((x◇x)◇((x◇x)◇(y◇(((((x◇x)◇((x◇x)◇(z◇((x◇x)◇(x◇x)))))◇(x◇(x◇x)))◇(x◇x))◇(x◇x)))))◇((x◇(x◇(u◇(x◇x))))◇((x◇(x◇(u◇(x◇x))))◇(w◇x))))=(x◇(x◇(u◇(x◇x)))):=by
   intro x y z u w
   exact l66 x y z u w
  have p6:∀ (x y z u:G),(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(x◇(x◇(u◇(x◇x)))))=x:=by
   intro x y z u
   exact l30 x y z u
  have p17x:∀ (A B C D E:G),(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(((A◇A)◇((A◇A)◇(D◇(((((A◇A)◇((A◇A)◇(E◇((A◇A)◇(A◇A)))))◇(A◇(A◇A)))◇(A◇A))◇(A◇A)))))◇(((A◇A)◇((A◇A)◇(D◇(((((A◇A)◇((A◇A)◇(E◇((A◇A)◇(A◇A)))))◇(A◇(A◇A)))◇(A◇A))◇(A◇A)))))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(A◇A)))))=((A◇A)◇((A◇A)◇(D◇(((((A◇A)◇((A◇A)◇(E◇((A◇A)◇(A◇A)))))◇(A◇(A◇A)))◇(A◇A))◇(A◇A))))):=by
   intro A B C D E
   let s0:G:=((A◇A)◇((A◇A)◇(D◇(((((A◇A)◇((A◇A)◇(E◇((A◇A)◇(A◇A)))))◇(A◇(A◇A)))◇(A◇A))◇(A◇A)))))
   let s1:G:=((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))
   let s2:G:=(s0◇(s0◇(s1◇(A◇A))))
   calc (s1◇s2)
    _=((s0◇(s1◇(A◇A)))◇s2):=K (S (p9 A D E B C)) rfl
    _=s0:=p7 ((A◇A)) D (((((A◇A)◇((A◇A)◇(E◇((A◇A)◇(A◇A)))))◇(A◇(A◇A)))◇(A◇A))) (s1)
  have p17:∀ (x y z:G),((x◇x)◇((x◇x)◇(y◇(((((x◇x)◇((x◇x)◇(z◇((x◇x)◇(x◇x)))))◇(x◇(x◇x)))◇(x◇x))◇(x◇x)))))=x:=by
   intro x y z
   let s0:G:=((x◇x)◇((x◇x)◇(y◇(((((x◇x)◇((x◇x)◇(z◇((x◇x)◇(x◇x)))))◇(x◇(x◇x)))◇(x◇x))◇(x◇x)))))
   let s1:G:=((x◇(x◇(x◇(x◇x))))◇((x◇(x◇(x◇(x◇x))))◇(x◇x)))
   have r0:(s1◇(s0◇(s0◇(s1◇(x◇x)))))=s0:=p17x x x x y z
   have r1:(s1◇(s0◇s1))=s0:=(K rfl (K rfl (p9 x y z x x))).symm.trans r0
   have r2:(s1◇(x◇(x◇(x◇(x◇x)))))=s0:=(K rfl (p8 x y z x x)).symm.trans r1
   have r3:x=s0:=(S (p6 x x x x)).trans r2
   exact S r3
  p17 B C D
 let l72:=fun (B C D E:G)=>
  have p4:∀ (x y z:G),(x◇((x◇(y◇(z◇x)))◇((x◇(y◇(z◇x)))◇x)))=(x◇(y◇(z◇x))):=by
   intro x y z
   exact l7 x y z
  have p6:∀ (x y z u:G),(x◇((((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y)))◇(((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y)))◇y))◇((((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y)))◇(((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y)))◇y))◇(y◇(y◇(z◇(x◇y)))))))=(((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y)))◇(((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y)))◇y)):=by
   intro x y z u
   exact l25 x y z u
  have p11x:∀ (A B C D:G),((A◇(B◇(C◇A)))◇((((A◇(A◇(B◇(C◇A))))◇((A◇(A◇((A◇(B◇(C◇A)))◇((A◇(B◇(C◇A)))◇A))))◇(D◇A)))◇(((A◇(A◇((A◇(B◇(C◇A)))◇((A◇(B◇(C◇A)))◇A))))◇((A◇(A◇((A◇(B◇(C◇A)))◇((A◇(B◇(C◇A)))◇A))))◇(D◇A)))◇A))◇((((A◇(A◇((A◇(B◇(C◇A)))◇((A◇(B◇(C◇A)))◇A))))◇((A◇(A◇((A◇(B◇(C◇A)))◇((A◇(B◇(C◇A)))◇A))))◇(D◇A)))◇(((A◇(A◇((A◇(B◇(C◇A)))◇((A◇(B◇(C◇A)))◇A))))◇((A◇(A◇((A◇(B◇(C◇A)))◇((A◇(B◇(C◇A)))◇A))))◇(D◇A)))◇A))◇(A◇(A◇((A◇(B◇(C◇A)))◇((A◇(B◇(C◇A)))◇A)))))))=(((A◇(A◇((A◇(B◇(C◇A)))◇((A◇(B◇(C◇A)))◇A))))◇((A◇(A◇((A◇(B◇(C◇A)))◇((A◇(B◇(C◇A)))◇A))))◇(D◇A)))◇(((A◇(A◇((A◇(B◇(C◇A)))◇((A◇(B◇(C◇A)))◇A))))◇((A◇(A◇((A◇(B◇(C◇A)))◇((A◇(B◇(C◇A)))◇A))))◇(D◇A)))◇A)):=by
   intro A B C D
   let s0:G:=(A◇(A◇((A◇(B◇(C◇A)))◇((A◇(B◇(C◇A)))◇A))))
   let s1:G:=((s0◇(s0◇(D◇A)))◇((s0◇(s0◇(D◇A)))◇A))
   let s2:G:=((A◇(B◇(C◇A))))
   calc ((A◇(B◇(C◇A)))◇((((A◇(A◇(B◇(C◇A))))◇(s0◇(D◇A)))◇((s0◇(s0◇(D◇A)))◇A))◇(s1◇s0)))
    _=((A◇(B◇(C◇A)))◇(s1◇(s1◇s0))):=K rfl (K (K (K (K rfl (S (p4 A B C))) rfl) rfl) rfl)
    _=s1:=p6 s2 A s2 D
  have p11:∀ (x y z u:G),((x◇(y◇(z◇x)))◇((((x◇(x◇(y◇(z◇x))))◇((x◇(x◇(y◇(z◇x))))◇(u◇x)))◇(((x◇(x◇(y◇(z◇x))))◇((x◇(x◇(y◇(z◇x))))◇(u◇x)))◇x))◇((((x◇(x◇(y◇(z◇x))))◇((x◇(x◇(y◇(z◇x))))◇(u◇x)))◇(((x◇(x◇(y◇(z◇x))))◇((x◇(x◇(y◇(z◇x))))◇(u◇x)))◇x))◇(x◇(x◇(y◇(z◇x)))))))=(((x◇(x◇(y◇(z◇x))))◇((x◇(x◇(y◇(z◇x))))◇(u◇x)))◇(((x◇(x◇(y◇(z◇x))))◇((x◇(x◇(y◇(z◇x))))◇(u◇x)))◇x)):=by
   intro x y z u
   simpa only [p4,p4,p4,p4,p4,p4,p4,p4,p4,p4,p4,p4] using (p11x x y z u)
  p11 B C D E
 let l73:=fun (B C D E:G)=>
  have p4:∀ (x y z u:G),(((x◇(x◇(y◇(z◇x))))◇((x◇(x◇(y◇(z◇x))))◇(u◇(x◇(x◇(x◇(y◇(z◇x))))))))◇(x◇(x◇(y◇(z◇x)))))=x:=by
   intro x y z u
   exact l12 x y z u
  have p5:∀ (x y z u w:G),(((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(u◇(x◇(x◇(y◇(x◇x)))))))◇((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(u◇(x◇(x◇(y◇(x◇x)))))))◇(w◇((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x))))))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(u◇(x◇(x◇(y◇(x◇x))))))))=((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x))):=by
   intro x y z u w
   exact l67 x y z u w
  have p9x:∀ (A B C D E:G),(((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A))◇((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(D◇(A◇(A◇(A◇(B◇(A◇A))))))))◇(A◇(A◇(B◇(A◇A)))))))◇(E◇((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A))))))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(D◇(A◇(A◇(A◇(B◇(A◇A))))))))◇(A◇(A◇(B◇(A◇A))))))))=((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A))):=by
   intro A B C D E
   let s0:G:=(A◇(A◇(B◇(A◇A))))
   let s1:G:=((s0◇(s0◇(C◇A)))◇((s0◇(s0◇(C◇A)))◇((s0◇(s0◇(D◇(A◇s0))))◇s0)))
   let s2:G:=(s1◇(E◇(s0◇(s0◇(C◇A)))))
   calc ((((s0◇(s0◇(C◇A)))◇((s0◇(s0◇(C◇A)))◇A))◇s2)◇s1)
    _=((s1◇s2)◇s1):=K (K (K rfl (K rfl (S (p4 A B A D)))) rfl) rfl
    _=(s0◇(s0◇(C◇A))):=p5 A B C ((s0◇(s0◇(D◇(A◇s0))))) E
  have p9:∀ (x y z u:G),(((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x))◇((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x))◇(u◇((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x))))))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)))=((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x))):=by
   intro x y z u
   let s0:G:=((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))
   let s1:G:=(s0◇(s0◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(x◇(x◇(x◇(x◇(y◇(x◇x))))))))◇(x◇(x◇(y◇(x◇x)))))))
   let s2:G:=((s0◇(s0◇x))◇((s0◇(s0◇x))◇(u◇s0)))
   have r0:(((s0◇(s0◇x))◇(s1◇(u◇s0)))◇s1)=s0:=p9x x y z x u
   have r1:(s2◇s1)=s0:=(K (K rfl (K (K rfl (K rfl (p4 x y x x))) rfl)) rfl).symm.trans r0
   have r2:(s2◇(s0◇(s0◇x)))=s0:=(K rfl (K rfl (K rfl (p4 x y x x)))).symm.trans r1
   exact r2
  p9 B C D E
 let l74x:=fun (A B C D E:G)=>
  let q0:G:=((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))
  let q1:G:=(q0◇(q0◇(D◇(q0◇q0))))
  calc ((q1◇(q1◇(E◇q0)))◇q0)
   _=(q0◇q0):=((l22 (q0) D E).symm).symm
   _=(A◇(A◇(B◇(A◇A)))):=l29 A B C B C
 let l74:=fun (B C D E F:G)=>
  let q0:G:=((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))
  let q1:G:=(B◇(B◇(C◇(B◇B))))
  let q2:G:=(q0◇(q0◇(E◇(q0◇q0))))
  have r0:((q2◇(q2◇(F◇q0)))◇q0)=q1:=l74x B C D E F
  have r1:(((q0◇(q0◇(E◇q1)))◇(q2◇(F◇q0)))◇q0)=q1:=(K (K (K rfl (K rfl (K rfl (l29 B C D C D)))) rfl) rfl).symm.trans r0
  have r2:(((q0◇(q0◇(E◇q1)))◇((q0◇(q0◇(E◇q1)))◇(F◇q0)))◇q0)=q1:=(K (K rfl (K (K rfl (K rfl (K rfl (l29 B C D C D)))) rfl)) rfl).symm.trans r1
  r2
 let l75:=fun (B C D E:G)=>
  have p4:∀ (x:G),((x◇(x◇x))◇(x◇(x◇x)))=(x◇(x◇(x◇x))):=by
   intro x
   exact l69 x
  have p5:∀ (x y z u:G),(((x◇x)◇((x◇x)◇(y◇(((((x◇x)◇((x◇x)◇(z◇((x◇x)◇(x◇x)))))◇(x◇(x◇x)))◇(x◇x))◇(x◇x)))))◇(x◇(x◇(u◇(x◇x)))))=x:=by
   intro x y z u
   exact l68 x y z u
  have p8x:∀ (A B C D:G),(((A◇(A◇(A◇A)))◇(((A◇(A◇A))◇(A◇(A◇A)))◇(B◇((((((A◇(A◇A))◇(A◇(A◇A)))◇(((A◇(A◇A))◇(A◇(A◇A)))◇(C◇(((A◇(A◇A))◇(A◇(A◇A)))◇((A◇(A◇A))◇(A◇(A◇A)))))))◇((A◇(A◇A))◇((A◇(A◇A))◇(A◇(A◇A)))))◇((A◇(A◇A))◇(A◇(A◇A))))◇((A◇(A◇A))◇(A◇(A◇A)))))))◇((A◇(A◇A))◇((A◇(A◇A))◇(D◇((A◇(A◇A))◇(A◇(A◇A)))))))=(A◇(A◇A)):=by
   intro A B C D
   let s0:G:=((A◇(A◇A))◇(A◇(A◇A)))
   let s1:G:=(s0◇(B◇((((s0◇(s0◇(C◇(s0◇s0))))◇((A◇(A◇A))◇s0))◇s0)◇s0)))
   let s2:G:=((A◇(A◇A))◇((A◇(A◇A))◇(D◇s0)))
   calc (((A◇(A◇(A◇A)))◇s1)◇s2)
    _=((s0◇s1)◇s2):=K (K (S (p4 A)) rfl) rfl
    _=(A◇(A◇A)):=p5 ((A◇(A◇A))) B C D
  have p8:∀ (x y z u:G),(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇(((((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(z◇((x◇(x◇(x◇x)))◇(x◇(x◇(x◇x)))))))◇((x◇(x◇x))◇(x◇(x◇(x◇x)))))◇(x◇(x◇(x◇x))))◇(x◇(x◇(x◇x)))))))◇((x◇(x◇x))◇((x◇(x◇x))◇(u◇(x◇(x◇(x◇x)))))))=(x◇(x◇x)):=by
   intro x y z u
   let s0:G:=((x◇(x◇x))◇(x◇(x◇x)))
   let s1:G:=(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(z◇((x◇(x◇(x◇x)))◇(x◇(x◇(x◇x)))))))◇((x◇(x◇x))◇(x◇(x◇(x◇x)))))
   let s2:G:=((x◇(x◇x))◇((x◇(x◇x))◇(u◇s0)))
   let s3:G:=((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇((s1◇(x◇(x◇(x◇x))))◇(x◇(x◇(x◇x)))))))
   let s4:G:=(y◇((((s0◇(s0◇(z◇(s0◇s0))))◇((x◇(x◇x))◇s0))◇s0)◇s0))
   have r0:(((x◇(x◇(x◇x)))◇(s0◇s4))◇s2)=(x◇(x◇x)):=p8x x y z u
   have r1:(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇s4))◇s2)=(x◇(x◇x)):=(K (K rfl (K (p4 x) rfl)) rfl).symm.trans r0
   have r2:(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇(((((x◇(x◇(x◇x)))◇(s0◇(z◇(s0◇s0))))◇((x◇(x◇x))◇s0))◇s0)◇s0))))◇s2)=(x◇(x◇x)):=(K (K rfl (K rfl (K rfl (K (K (K (K (p4 x) rfl) rfl) rfl) rfl)))) rfl).symm.trans r1
   have r3:(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇(((((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(z◇(s0◇s0))))◇((x◇(x◇x))◇s0))◇s0)◇s0))))◇s2)=(x◇(x◇x)):=(K (K rfl (K rfl (K rfl (K (K (K (K rfl (K (p4 x) rfl)) rfl) rfl) rfl)))) rfl).symm.trans r2
   have r4:(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇(((((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(z◇((x◇(x◇(x◇x)))◇s0))))◇((x◇(x◇x))◇s0))◇s0)◇s0))))◇s2)=(x◇(x◇x)):=(K (K rfl (K rfl (K rfl (K (K (K (K rfl (K rfl (K rfl (K (p4 x) rfl)))) rfl) rfl) rfl)))) rfl).symm.trans r3
   have r5:(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇(((((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(z◇((x◇(x◇(x◇x)))◇(x◇(x◇(x◇x)))))))◇((x◇(x◇x))◇s0))◇s0)◇s0))))◇s2)=(x◇(x◇x)):=(K (K rfl (K rfl (K rfl (K (K (K (K rfl (K rfl (K rfl (K rfl (p4 x))))) rfl) rfl) rfl)))) rfl).symm.trans r4
   have r6:(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇((s1◇s0)◇s0))))◇s2)=(x◇(x◇x)):=(K (K rfl (K rfl (K rfl (K (K (K rfl (K rfl (p4 x))) rfl) rfl)))) rfl).symm.trans r5
   have r7:(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇((s1◇(x◇(x◇(x◇x))))◇s0))))◇s2)=(x◇(x◇x)):=(K (K rfl (K rfl (K rfl (K (K rfl (p4 x)) rfl)))) rfl).symm.trans r6
   have r8:(s3◇s2)=(x◇(x◇x)):=(K (K rfl (K rfl (K rfl (K rfl (p4 x))))) rfl).symm.trans r7
   have r9:(s3◇((x◇(x◇x))◇((x◇(x◇x))◇(u◇(x◇(x◇(x◇x)))))))=(x◇(x◇x)):=(K rfl (K rfl (K rfl (K rfl (p4 x))))).symm.trans r8
   exact r9
  p8 B C D E
 let l76:=fun (B C D:G)=>
  have p4:∀ (x y z:G),(((x◇(x◇(y◇(x◇x))))◇(z◇x))◇(x◇(x◇(y◇(x◇x)))))=x:=by
   intro x y z
   exact l58 x y z
  have p5:∀ (x y z u:G),((((x◇(x◇(y◇(z◇x))))◇(u◇x))◇(x◇(x◇(y◇(z◇x)))))◇(((x◇(x◇(y◇(z◇x))))◇(u◇x))◇(((x◇(x◇(y◇(z◇x))))◇(u◇x))◇(x◇(x◇(y◇(z◇x)))))))=((x◇(x◇(y◇(z◇x))))◇(u◇x)):=by
   intro x y z u
   exact l70 x y z u
  have p11x:∀ (A B C:G),(A◇(((A◇(A◇(B◇(A◇A))))◇(C◇A))◇(((A◇(A◇(B◇(A◇A))))◇(C◇A))◇(A◇(A◇(B◇(A◇A)))))))=((A◇(A◇(B◇(A◇A))))◇(C◇A)):=by
   intro A B C
   let s0:G:=(A◇(A◇(B◇(A◇A))))
   let s1:G:=((s0◇(C◇A))◇((s0◇(C◇A))◇s0))
   calc (A◇s1)
    _=(((s0◇(C◇A))◇s0)◇s1):=K (S (p4 A B C)) rfl
    _=(s0◇(C◇A)):=p5 A B A C
  have p11:∀ (x y z:G),(x◇(((x◇(x◇(y◇(x◇x))))◇(z◇x))◇x))=((x◇(x◇(y◇(x◇x))))◇(z◇x)):=by
   intro x y z
   let s0:G:=((x◇(x◇(y◇(x◇x))))◇(z◇x))
   have r0:(x◇(s0◇(s0◇(x◇(x◇(y◇(x◇x)))))))=s0:=p11x x y z
   have r1:(x◇(s0◇x))=s0:=(K rfl (K rfl (p4 x y z))).symm.trans r0
   exact r1
  p11 B C D
 let l77:=fun (B C:G)=>
  let q0:G:=(((B◇B)◇((B◇B)◇(C◇((B◇B)◇(B◇B)))))◇(B◇(B◇B)))
  calc (q0◇(B◇B))
   _=(((B◇B)◇((B◇B)◇(B◇((q0◇(B◇B))◇(B◇B)))))◇(B◇B)):=(l5 ((B◇B)) B (q0)).symm
   _=(B◇(B◇B)):=K (l71 B B C) rfl
 let l78:=fun (B C D:G)=>
  let q0:G:=((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))
  let q1:G:=(B◇(B◇(C◇(B◇B))))
  calc ((B◇(C◇(B◇B)))◇((q0◇(B◇B))◇((q0◇(B◇B))◇q1)))
   _=((B◇(C◇(B◇B)))◇((q0◇(q0◇B))◇((q0◇(B◇B))◇q1))):=K rfl (K (K rfl (S (l22 B C D))) rfl)
   _=((B◇(C◇(B◇B)))◇((q0◇(q0◇B))◇((q0◇(q0◇B))◇q1))):=K rfl (K rfl (K (K rfl (S (l22 B C D))) rfl))
   _=(q0◇(q0◇B)):=(S (l72 B C B D)).symm
   _=(q0◇(B◇B)):=K rfl ((S (l22 B C D)).symm)
 let l79:=fun (B C D:G)=>
  let q0:G:=((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))
  let q1:G:=(B◇(B◇(C◇(B◇B))))
  calc (((q0◇(q0◇B))◇((q0◇(q0◇B))◇q1))◇(q0◇(q0◇B)))
   _=(((q0◇(q0◇B))◇((q0◇(q0◇B))◇((q1◇(D◇B))◇q0)))◇(q0◇(q0◇B))):=K (K rfl (K rfl (S (l17 B C B D)))) rfl
   _=q0:=l73 B C D ((q1◇(D◇B)))
 let l80:=fun (B C D E:G)=>
  have p6:∀ (x y z u:G),(((x◇(x◇(y◇(z◇x))))◇((x◇(x◇(y◇(z◇x))))◇(u◇(x◇(x◇(x◇(y◇(z◇x))))))))◇(x◇(x◇(y◇(z◇x)))))=x:=by
   intro x y z u
   exact l12 x y z u
  have p7:∀ (x y z u w:G),(((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(u◇(x◇(x◇(y◇(x◇x)))))))◇((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(u◇(x◇(x◇(y◇(x◇x)))))))◇(w◇((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x))))))◇((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x))))=(x◇(x◇(y◇(x◇x)))):=by
   intro x y z u w
   exact l74 x y z u w
  have p5:∀ (x y z:G),(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇x)=(x◇x):=by
   intro x y z
   exact l22 x y z
  have p13x:∀ (A B C D E:G),(((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇A))◇((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(D◇(A◇(A◇(A◇(B◇(A◇A))))))))◇(A◇(A◇(B◇(A◇A)))))))◇(E◇((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A))))))◇((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A))))=(A◇(A◇(B◇(A◇A)))):=by
   intro A B C D E
   let s0:G:=(A◇(A◇(B◇(A◇A))))
   let s1:G:=((s0◇(s0◇(C◇A)))◇((s0◇(s0◇(C◇A)))◇((s0◇(s0◇(D◇(A◇s0))))◇s0)))
   let s2:G:=(s1◇(E◇(s0◇(s0◇(C◇A)))))
   calc ((((s0◇(s0◇(C◇A)))◇((s0◇(s0◇(C◇A)))◇A))◇s2)◇(s0◇(s0◇(C◇A))))
    _=((s1◇s2)◇(s0◇(s0◇(C◇A)))):=K (K (K rfl (K rfl (S (p6 A B A D)))) rfl) rfl
    _=s0:=p7 A B C ((s0◇(s0◇(D◇(A◇s0))))) E
  have p13:∀ (x y z u:G),(((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(x◇x))◇((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(x◇x))◇(u◇((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x))))))◇((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x))))=(x◇(x◇(y◇(x◇x)))):=by
   intro x y z u
   let s0:G:=((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))
   let s1:G:=(x◇(x◇(y◇(x◇x))))
   let s2:G:=((s0◇(s0◇((s1◇(s1◇(x◇(x◇s1))))◇s1)))◇(u◇s0))
   have r0:(((s0◇(s0◇x))◇s2)◇s0)=s1:=p13x x y z x u
   have r1:(((s0◇(x◇x))◇s2)◇s0)=s1:=(K (K (K rfl (p5 x y z)) rfl) rfl).symm.trans r0
   have r2:(((s0◇(x◇x))◇((s0◇(s0◇x))◇(u◇s0)))◇s0)=s1:=(K (K rfl (K (K rfl (K rfl (p6 x y x x))) rfl)) rfl).symm.trans r1
   have r3:(((s0◇(x◇x))◇((s0◇(x◇x))◇(u◇s0)))◇s0)=s1:=(K (K rfl (K (K rfl (p5 x y z)) rfl)) rfl).symm.trans r2
   exact r3
  p13 B C D E
 let l81:=fun (B C D:G)=>
  have p6:∀ (x y:G),((x◇(x◇x))◇(x◇(x◇(y◇(x◇x)))))=x:=by
   intro x y
   exact l40 x y
  have p7:∀ (x y z u:G),(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇(((((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(z◇((x◇(x◇(x◇x)))◇(x◇(x◇(x◇x)))))))◇((x◇(x◇x))◇(x◇(x◇(x◇x)))))◇(x◇(x◇(x◇x))))◇(x◇(x◇(x◇x)))))))◇((x◇(x◇x))◇((x◇(x◇x))◇(u◇(x◇(x◇(x◇x)))))))=(x◇(x◇x)):=by
   intro x y z u
   exact l75 x y z u
  have p5:∀ (x:G),((x◇(x◇x))◇x)=(x◇x):=by
   intro x
   exact l38 x
  have p9x:∀ (A B C:G),(((A◇(A◇(A◇A)))◇((A◇(A◇(A◇A)))◇(B◇(((((A◇(A◇(A◇A)))◇((A◇(A◇(A◇A)))◇(C◇((A◇(A◇(A◇A)))◇(A◇(A◇(A◇A)))))))◇((A◇(A◇A))◇(A◇(A◇(A◇A)))))◇(A◇(A◇(A◇A))))◇(A◇(A◇(A◇A)))))))◇((A◇(A◇A))◇A))=(A◇(A◇A)):=by
   intro A B C
   let s0:G:=((A◇(A◇(A◇A)))◇((A◇(A◇(A◇A)))◇(B◇(((((A◇(A◇(A◇A)))◇((A◇(A◇(A◇A)))◇(C◇((A◇(A◇(A◇A)))◇(A◇(A◇(A◇A)))))))◇((A◇(A◇A))◇(A◇(A◇(A◇A)))))◇(A◇(A◇(A◇A))))◇(A◇(A◇(A◇A)))))))
   calc (s0◇((A◇(A◇A))◇A))
    _=(s0◇((A◇(A◇A))◇((A◇(A◇A))◇(A◇(A◇(A◇(A◇A))))))):=K rfl (K rfl (S (p6 A A)))
    _=(A◇(A◇A)):=p7 A B C A
  have p9:∀ (x y z:G),(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇(((((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(z◇((x◇(x◇(x◇x)))◇(x◇(x◇(x◇x)))))))◇((x◇(x◇x))◇(x◇(x◇(x◇x)))))◇(x◇(x◇(x◇x))))◇(x◇(x◇(x◇x)))))))◇(x◇x))=(x◇(x◇x)):=by
   intro x y z
   let s0:G:=((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇(((((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(z◇((x◇(x◇(x◇x)))◇(x◇(x◇(x◇x)))))))◇((x◇(x◇x))◇(x◇(x◇(x◇x)))))◇(x◇(x◇(x◇x))))◇(x◇(x◇(x◇x)))))))
   have r0:(s0◇((x◇(x◇x))◇x))=(x◇(x◇x)):=p9x x y z
   have r1:(s0◇(x◇x))=(x◇(x◇x)):=(K rfl (p5 x)).symm.trans r0
   exact r1
  p9 B C D
 let l82:=fun (B C:G)=>
  let q0:G:=(((B◇B)◇((B◇B)◇(C◇((B◇B)◇(B◇B)))))◇(B◇(B◇B)))
  calc q0
   _=((B◇B)◇(q0◇(B◇B))):=(l76 ((B◇B)) C B).symm
   _=((B◇B)◇(B◇(B◇B))):=K rfl (l77 B C)
 let l83:=fun (B C D E:G)=>
  let q0:G:=((((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))◇(B◇B))◇((((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))◇(B◇B))◇(B◇(B◇(C◇(B◇B))))))
  let q1:G:=(B◇(B◇(C◇(B◇B))))
  calc ((B◇(C◇(B◇B)))◇(q0◇(q0◇(E◇((q1◇(q1◇(D◇B)))◇(B◇B))))))
   _=((B◇(C◇(B◇B)))◇(q0◇(q0◇(E◇((B◇(C◇(B◇B)))◇q0))))):=K rfl (K rfl (K rfl (K rfl (S (l78 B C D)))))
   _=q0:=(l3 (q0) ((B◇(C◇(B◇B)))) E).symm
 let l84:=fun (B C D:G)=>
  let q0:G:=((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))
  let q1:G:=((q0◇(q0◇B))◇(B◇(B◇(C◇(B◇B)))))
  calc (((q0◇(B◇B))◇((q0◇(B◇B))◇(B◇(B◇(C◇(B◇B))))))◇(q0◇(B◇B)))
   _=(((q0◇(B◇B))◇q1)◇(q0◇(B◇B))):=K (K rfl (K (K rfl (S (l22 B C D))) rfl)) rfl
   _=(((q0◇(B◇B))◇q1)◇(q0◇(q0◇B))):=K rfl (K rfl (S (l22 B C D)))
   _=(((q0◇(q0◇B))◇q1)◇(q0◇(q0◇B))):=K (K (K rfl (S (l22 B C D))) rfl) rfl
   _=q0:=(S (l79 B C D)).symm
 let l85:=fun (B C D:G)=>
  let q0:G:=((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))
  let q1:G:=((q0◇(B◇B))◇((q0◇(B◇B))◇(B◇q0)))
  let q2:G:=(B◇(B◇(C◇(B◇B))))
  calc (((q0◇(B◇B))◇((q0◇(B◇B))◇q2))◇q0)
   _=(((q0◇(B◇B))◇((q0◇(B◇B))◇(q1◇q0)))◇q0):=K (K rfl (K rfl (S (l80 B C D B)))) rfl
   _=q2:=l80 B C D (q1)
 let l86x:=fun (A B C D:G)=>
  let q0:G:=((A◇(A◇(A◇A)))◇((A◇(A◇(A◇A)))◇(B◇(((((A◇(A◇(A◇A)))◇((A◇(A◇(A◇A)))◇(C◇((A◇(A◇(A◇A)))◇(A◇(A◇(A◇A)))))))◇((A◇(A◇A))◇(A◇(A◇(A◇A)))))◇(A◇(A◇(A◇A))))◇(A◇(A◇(A◇A)))))))
  calc (A◇A)
   _=(q0◇((A◇A)◇((A◇A)◇(D◇(q0◇(A◇A)))))):=l3 ((A◇A)) (q0) D
   _=(q0◇((A◇A)◇((A◇A)◇(D◇(A◇(A◇A)))))):=K rfl (K rfl (K rfl (K rfl (l81 A B C))))
 let l86:=fun (B C D:G)=>
  let q0:G:=((B◇(B◇(B◇B)))◇((B◇(B◇(B◇B)))◇(C◇(((((B◇(B◇(B◇B)))◇((B◇(B◇(B◇B)))◇(D◇((B◇(B◇(B◇B)))◇(B◇(B◇(B◇B)))))))◇((B◇(B◇B))◇(B◇(B◇(B◇B)))))◇(B◇(B◇(B◇B))))◇(B◇(B◇(B◇B)))))))
  have r0:(B◇B)=(q0◇((B◇B)◇((B◇B)◇(B◇(B◇(B◇B)))))):=l86x B C D B
  have r1:(B◇B)=(q0◇B):=r0.trans (K rfl (l43 B B))
  S r1
 let l87:=fun (B:G)=>
  calc (((B◇B)◇(B◇(B◇B)))◇(B◇B))
   _=((((B◇B)◇((B◇B)◇(B◇((B◇B)◇(B◇B)))))◇(B◇(B◇B)))◇(B◇B)):=K (S (l82 B B)) rfl
   _=(B◇(B◇B)):=l77 B B
 let l88x:=fun (A B C:G)=>
  let q0:G:=((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(A◇A))◇((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(A◇A))◇(A◇(A◇(B◇(A◇A))))))
  let q1:G:=(A◇(A◇(B◇(A◇A))))
  calc ((A◇(B◇(A◇A)))◇(q0◇(q0◇(q1◇(q1◇(C◇A))))))
   _=((A◇(B◇(A◇A)))◇(q0◇(q0◇(q0◇((q1◇(q1◇(C◇A)))◇(A◇A)))))):=K rfl (K rfl (K rfl (S (l84 A B C))))
   _=q0:=l83 A B C (q0)
 let l88:=fun (B C D:G)=>
  let q0:G:=((((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))◇(B◇B))◇((((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))◇(B◇B))◇(B◇(B◇(C◇(B◇B))))))
  let q1:G:=(B◇(B◇(C◇(B◇B))))
  have r0:((B◇(C◇(B◇B)))◇(q0◇(q0◇(q1◇(q1◇(D◇B))))))=q0:=l88x B C D
  have r1:((B◇(C◇(B◇B)))◇(q0◇q1))=q0:=(K rfl (K rfl (l85 B C D))).symm.trans r0
  r1
 let l89:=fun (B C D:G)=>
  let q0:G:=((B◇(B◇(C◇(B◇B))))◇((B◇(B◇(C◇(B◇B))))◇(D◇B)))
  calc (B◇(q0◇(B◇B)))
   _=(B◇(q0◇(q0◇B))):=K rfl (K rfl (S (l22 B C D)))
   _=q0:=l14 B B C D
 let l90:=fun (B:G)=>
  let q0:G:=((B◇(B◇B))◇((B◇(B◇B))◇(B◇(B◇B))))
  let q1:G:=((B◇(B◇B))◇(B◇(B◇(B◇B))))
  calc (q1◇q1)
   _=(q0◇q1):=K (K rfl (S (l69 B))) rfl
   _=(q0◇q0):=K rfl (K rfl (S (l69 B)))
   _=((B◇(B◇B))◇q0):=((l69 ((B◇(B◇B)))).symm).symm
   _=((B◇(B◇B))◇q1):=K rfl (K rfl ((S (l69 B)).symm))
 let l91:=fun (B C D E F:G)=>
  have p6:∀ (x y z:G),(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇(((((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(z◇((x◇(x◇(x◇x)))◇(x◇(x◇(x◇x)))))))◇((x◇(x◇x))◇(x◇(x◇(x◇x)))))◇(x◇(x◇(x◇x))))◇(x◇(x◇(x◇x)))))))◇x)=(x◇x):=by
   intro x y z
   exact l86 x y z
  have p5:∀ (x y z u:G),(x◇((y◇(y◇(z◇(x◇y))))◇((y◇(y◇(z◇(x◇y))))◇(u◇y))))=(y◇(y◇(z◇(x◇y)))):=by
   intro x y z u
   exact l4 x y z u
  have p10x:∀ (A B C D E:G),(((A◇(A◇(A◇A)))◇((A◇(A◇(A◇A)))◇(B◇(((((A◇(A◇(A◇A)))◇((A◇(A◇(A◇A)))◇(C◇((A◇(A◇(A◇A)))◇(A◇(A◇(A◇A)))))))◇((A◇(A◇A))◇(A◇(A◇(A◇A)))))◇(A◇(A◇(A◇A))))◇(A◇(A◇(A◇A)))))))◇((A◇(A◇(D◇(A◇A))))◇((A◇(A◇(D◇(((A◇(A◇(A◇A)))◇((A◇(A◇(A◇A)))◇(B◇(((((A◇(A◇(A◇A)))◇((A◇(A◇(A◇A)))◇(C◇((A◇(A◇(A◇A)))◇(A◇(A◇(A◇A)))))))◇((A◇(A◇A))◇(A◇(A◇(A◇A)))))◇(A◇(A◇(A◇A))))◇(A◇(A◇(A◇A)))))))◇A))))◇(E◇A))))=(A◇(A◇(D◇(((A◇(A◇(A◇A)))◇((A◇(A◇(A◇A)))◇(B◇(((((A◇(A◇(A◇A)))◇((A◇(A◇(A◇A)))◇(C◇((A◇(A◇(A◇A)))◇(A◇(A◇(A◇A)))))))◇((A◇(A◇A))◇(A◇(A◇(A◇A)))))◇(A◇(A◇(A◇A))))◇(A◇(A◇(A◇A)))))))◇A)))):=by
   intro A B C D E
   let s0:G:=((A◇(A◇(A◇A)))◇((A◇(A◇(A◇A)))◇(B◇(((((A◇(A◇(A◇A)))◇((A◇(A◇(A◇A)))◇(C◇((A◇(A◇(A◇A)))◇(A◇(A◇(A◇A)))))))◇((A◇(A◇A))◇(A◇(A◇(A◇A)))))◇(A◇(A◇(A◇A))))◇(A◇(A◇(A◇A)))))))
   let s1:G:=(A◇(A◇(D◇(s0◇A))))
   calc (s0◇((A◇(A◇(D◇(A◇A))))◇(s1◇(E◇A))))
    _=(s0◇(s1◇(s1◇(E◇A)))):=K rfl (K (K rfl (K rfl (K rfl (S (p6 A B C))))) rfl)
    _=s1:=p5 (s0) A D E
  have p10:∀ (x y z u w:G),(((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇(((((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(z◇((x◇(x◇(x◇x)))◇(x◇(x◇(x◇x)))))))◇((x◇(x◇x))◇(x◇(x◇(x◇x)))))◇(x◇(x◇(x◇x))))◇(x◇(x◇(x◇x)))))))◇((x◇(x◇(u◇(x◇x))))◇((x◇(x◇(u◇(x◇x))))◇(w◇x))))=(x◇(x◇(u◇(x◇x)))):=by
   intro x y z u w
   let s0:G:=((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(y◇(((((x◇(x◇(x◇x)))◇((x◇(x◇(x◇x)))◇(z◇((x◇(x◇(x◇x)))◇(x◇(x◇(x◇x)))))))◇((x◇(x◇x))◇(x◇(x◇(x◇x)))))◇(x◇(x◇(x◇x))))◇(x◇(x◇(x◇x)))))))
   let s1:G:=(x◇(x◇(u◇(x◇x))))
   let s2:G:=(x◇(x◇(u◇(s0◇x))))
   let s3:G:=(s0◇(s1◇(s1◇(w◇x))))
   have r0:(s0◇(s1◇(s2◇(w◇x))))=s2:=p10x x y z u w
   have r1:s3=s2:=(K rfl (K rfl (K (K rfl (K rfl (K rfl (p6 x y z)))) rfl))).symm.trans r0
   have r2:s3=s1:=r1.trans (K rfl (K rfl (K rfl (p6 x y z))))
   exact r2
  p10 B C D E F
 let l92:=fun (B C:G)=>
  let q0:G:=((B◇(B◇B))◇(B◇(B◇B)))
  let q1:G:=((B◇(B◇B))◇(B◇(B◇(B◇B))))
  let q2:G:=(C◇((B◇(B◇(B◇B)))◇(B◇(B◇(B◇B)))))
  let q3:G:=((B◇(B◇(B◇B)))◇(q0◇(C◇(q0◇q0))))
  calc (((B◇(B◇(B◇B)))◇((B◇(B◇(B◇B)))◇q2))◇q1)
   _=(((B◇(B◇(B◇B)))◇(q0◇q2))◇q1):=K (K rfl (K (S (l69 B)) rfl)) rfl
   _=(((B◇(B◇(B◇B)))◇(q0◇(C◇(q0◇(B◇(B◇(B◇B)))))))◇q1):=K (K rfl (K rfl (K rfl (K (S (l69 B)) rfl)))) rfl
   _=(q3◇q1):=K (K rfl (K rfl (K rfl (K rfl (S (l69 B)))))) rfl
   _=(q3◇((B◇(B◇B))◇q0)):=K rfl (K rfl (S (l69 B)))
   _=((q0◇(q0◇(C◇(q0◇q0))))◇((B◇(B◇B))◇q0)):=K (K (S (l69 B)) rfl) rfl
   _=(q0◇((B◇(B◇B))◇q0)):=((l82 ((B◇(B◇B))) C).symm).symm
   _=(q0◇q1):=K rfl (K rfl ((S (l69 B)).symm))
   _=((B◇(B◇(B◇B)))◇q1):=K ((S (l69 B)).symm) rfl
 let l93:=fun (B:G)=>
  let q0:G:=((B◇(B◇B))◇(B◇(B◇B)))
  let q1:G:=((B◇(B◇B))◇(B◇(B◇(B◇B))))
  let q2:G:=(q0◇((B◇(B◇B))◇q0))
  calc (((B◇(B◇(B◇B)))◇q1)◇(B◇(B◇(B◇B))))
   _=((q0◇q1)◇(B◇(B◇(B◇B)))):=K (K (S (l69 B)) rfl) rfl
   _=(q2◇(B◇(B◇(B◇B)))):=K (K rfl (K rfl (S (l69 B)))) rfl
   _=(q2◇q0):=K rfl (S (l69 B))
   _=((B◇(B◇B))◇q0):=((l87 ((B◇(B◇B)))).symm).symm
   _=q1:=K rfl ((S (l69 B)).symm)
 let l94:=fun (B:G)=>
  let q0:G:=((B◇(B◇B))◇((B◇(B◇B))◇(B◇(B◇B))))
  let q1:G:=((B◇(B◇B))◇(B◇(B◇(B◇B))))
  calc (q1◇(B◇(B◇(B◇B))))
   _=(q0◇(B◇(B◇(B◇B)))):=K (K rfl (S (l69 B))) rfl
   _=(q0◇((B◇(B◇B))◇(B◇(B◇B)))):=K rfl (S (l69 B))
   _=q0:=((l39 ((B◇(B◇B)))).symm).symm
   _=q1:=K rfl ((S (l69 B)).symm)
 let l95x:=fun (A B:G)=>
  let q0:G:=((A◇(A◇A))◇(A◇(A◇A)))
  let q1:G:=(q0◇(B◇((A◇(A◇A))◇q0)))
  calc ((A◇(A◇(A◇A)))◇q1)
   _=(q0◇q1):=K (S (l69 A)) rfl
   _=(A◇(A◇A)):=l43 ((A◇(A◇A))) B
 let l95:=fun (B C:G)=>
  let q0:G:=((B◇(B◇B))◇(B◇(B◇B)))
  let q1:G:=(C◇((B◇(B◇B))◇q0))
  have r0:((B◇(B◇(B◇B)))◇(q0◇q1))=(B◇(B◇B)):=l95x B C
  have r1:((B◇(B◇(B◇B)))◇((B◇(B◇(B◇B)))◇q1))=(B◇(B◇B)):=(K rfl (K (l69 B) rfl)).symm.trans r0
  have r2:((B◇(B◇(B◇B)))◇((B◇(B◇(B◇B)))◇(C◇((B◇(B◇B))◇(B◇(B◇(B◇B)))))))=(B◇(B◇B)):=(K rfl (K rfl (K rfl (K rfl (l69 B))))).symm.trans r1
  r2
 let l96:=fun (B C D:G)=>
  have p12:∀ (x y z:G),((x◇(y◇(x◇x)))◇(((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(x◇x))◇((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(x◇x))◇(x◇(x◇(y◇(x◇x))))))◇(x◇(x◇(y◇(x◇x))))))=((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(x◇x))◇((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(x◇x))◇(x◇(x◇(y◇(x◇x)))))):=by
   intro x y z
   exact l88 x y z
  have p6:∀ (x y z:G),(x◇(y◇(y◇(z◇(x◇y)))))=y:=by
   intro x y z
   exact S (l3 y x z)
  have p10:∀ (x y z:G),((x◇(y◇(x◇x)))◇((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(x◇x))◇((((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(x◇x))◇(x◇(x◇(y◇(x◇x)))))))=(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(x◇x)):=by
   intro x y z
   exact l78 x y z
  have p8:∀ (x y z:G),(x◇(((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))◇(x◇x)))=((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x))):=by
   intro x y z
   exact l89 x y z
  have p21x:∀ (A B C:G),(A◇((A◇(B◇(A◇A)))◇((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(A◇A))◇((((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(A◇A))◇(A◇(A◇(B◇(A◇A))))))))=(A◇(B◇(A◇A))):=by
   intro A B C
   let s0:G:=(((A◇(A◇(B◇(A◇A))))◇((A◇(A◇(B◇(A◇A))))◇(C◇A)))◇(A◇A))
   let s1:G:=(s0◇(s0◇(A◇(A◇(B◇(A◇A))))))
   calc (A◇((A◇(B◇(A◇A)))◇s1))
    _=(A◇((A◇(B◇(A◇A)))◇((A◇(B◇(A◇A)))◇(s1◇(A◇(A◇(B◇(A◇A)))))))):=K rfl (K rfl (S (p12 A B C)))
    _=(A◇(B◇(A◇A))):=p6 A ((A◇(B◇(A◇A)))) (s1)
  have p21:∀ (x y z:G),((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))=(x◇(y◇(x◇x))):=by
   intro x y z
   let s0:G:=((x◇(x◇(y◇(x◇x))))◇((x◇(x◇(y◇(x◇x))))◇(z◇x)))
   have r0:(x◇((x◇(y◇(x◇x)))◇((s0◇(x◇x))◇((s0◇(x◇x))◇(x◇(x◇(y◇(x◇x))))))))=(x◇(y◇(x◇x))):=p21x x y z
   have r1:(x◇(s0◇(x◇x)))=(x◇(y◇(x◇x))):=(K rfl (p10 x y z)).symm.trans r0
   have r2:s0=(x◇(y◇(x◇x))):=(S (p8 x y z)).trans r1
   exact r2
  p21 B C D
 let l97:=fun (B C:G)=>
  let q0:G:=((B◇(B◇B))◇(B◇(B◇(B◇B))))
  let q1:G:=(q0◇(q0◇(C◇((q0◇q0)◇q0))))
  calc ((q0◇(q0◇(C◇(((B◇(B◇B))◇q0)◇q0))))◇((B◇(B◇B))◇q0))
   _=(q1◇((B◇(B◇B))◇q0)):=K (K rfl (K rfl (K rfl (K (S (l90 B)) rfl)))) rfl
   _=(q1◇(q0◇q0)):=K rfl (S (l90 B))
   _=(q0◇(q0◇q0)):=((l26 (q0) C).symm).symm
   _=(q0◇((B◇(B◇B))◇q0)):=K rfl ((S (l90 B)).symm)
 let l98:=fun (B C:G)=>
  let q0:G:=(B◇(B◇(C◇(B◇B))))
  let q1:G:=((B◇(B◇B))◇(B◇(B◇(B◇B))))
  have r0:(((B◇(B◇(B◇B)))◇((B◇(B◇(B◇B)))◇(B◇(((((B◇(B◇(B◇B)))◇((B◇(B◇(B◇B)))◇(B◇((B◇(B◇(B◇B)))◇(B◇(B◇(B◇B)))))))◇q1)◇(B◇(B◇(B◇B))))◇(B◇(B◇(B◇B)))))))◇(q0◇(q0◇(B◇B))))=q0:=l91 B B B C B
  have r1:(((B◇(B◇(B◇B)))◇((B◇(B◇(B◇B)))◇(B◇((((B◇(B◇(B◇B)))◇q1)◇(B◇(B◇(B◇B))))◇(B◇(B◇(B◇B)))))))◇(q0◇(q0◇(B◇B))))=q0:=(K (K rfl (K rfl (K rfl (K (K (l92 B B) rfl) rfl)))) rfl).symm.trans r0
  have r2:(((B◇(B◇(B◇B)))◇((B◇(B◇(B◇B)))◇(B◇(q1◇(B◇(B◇(B◇B)))))))◇(q0◇(q0◇(B◇B))))=q0:=(K (K rfl (K rfl (K rfl (K (l93 B) rfl)))) rfl).symm.trans r1
  have r3:(((B◇(B◇(B◇B)))◇((B◇(B◇(B◇B)))◇(B◇q1)))◇(q0◇(q0◇(B◇B))))=q0:=(K (K rfl (K rfl (K rfl (l94 B)))) rfl).symm.trans r2
  have r4:((B◇(B◇B))◇(q0◇(q0◇(B◇B))))=q0:=(K (l95 B B) rfl).symm.trans r3
  have r5:((B◇(B◇B))◇(B◇(C◇(B◇B))))=q0:=(K rfl (l96 B C B)).symm.trans r4
  r5
 let l99:=fun (B C:G)=>
  let q0:G:=(B◇(B◇(C◇(B◇B))))
  calc ((B◇(C◇(B◇B)))◇B)
   _=((q0◇(q0◇(B◇B)))◇B):=K (S (l96 B C B)) rfl
   _=(B◇B):=l22 B C B
 let l100:=fun (B:G)=>
  let q0:G:=((B◇(B◇B))◇((B◇(B◇B))◇(B◇(B◇B))))
  let q1:G:=((B◇(B◇B))◇((B◇(B◇B))◇(B◇(B◇(B◇B)))))
  let q2:G:=(q0◇((B◇(B◇B))◇q0))
  let q3:G:=(((B◇(B◇B))◇(B◇(B◇(B◇B))))◇q1)
  calc (q3◇q1)
   _=((q0◇q1)◇q1):=K (K (K rfl (S (l69 B))) rfl) rfl
   _=(q2◇q1):=K (K rfl (K rfl (K rfl (S (l69 B))))) rfl
   _=(q2◇((B◇(B◇B))◇q0)):=K rfl (K rfl (K rfl (S (l69 B))))
   _=q2:=((l94 ((B◇(B◇B)))).symm).symm
   _=(q0◇q1):=K rfl (K rfl (K rfl ((S (l69 B)).symm)))
   _=q3:=K (K rfl ((S (l69 B)).symm)) rfl
 let l101:=fun (B:G)=>
  let q0:G:=((B◇(B◇B))◇(B◇(B◇(B◇B))))
  let q1:G:=(B◇(B◇(B◇(B◇B))))
  let q2:G:=(q0◇((B◇(B◇B))◇q0))
  let q3:G:=(B◇(((B◇(B◇B))◇q0)◇q0))
  have r0:((q0◇(q0◇q3))◇((B◇(B◇B))◇q0))=q2:=l97 B B
  have r1:((q1◇(q0◇q3))◇((B◇(B◇B))◇q0))=q2:=(K (K (l98 B B) rfl) rfl).symm.trans r0
  have r2:((q1◇(q1◇q3))◇((B◇(B◇B))◇q0))=q2:=(K (K rfl (K (l98 B B) rfl)) rfl).symm.trans r1
  have r3:((q1◇(q1◇(B◇(((B◇(B◇B))◇q1)◇q0))))◇((B◇(B◇B))◇q0))=q2:=(K (K rfl (K rfl (K rfl (K (K rfl (l98 B B)) rfl)))) rfl).symm.trans r2
  have r4:((q1◇(q1◇(B◇(B◇q0))))◇((B◇(B◇B))◇q0))=q2:=(K (K rfl (K rfl (K rfl (K (l40 B B) rfl)))) rfl).symm.trans r3
  have r5:((q1◇(q1◇(B◇(B◇q1))))◇((B◇(B◇B))◇q0))=q2:=(K (K rfl (K rfl (K rfl (K rfl (l98 B B))))) rfl).symm.trans r4
  have r6:((q1◇(q1◇(B◇B)))◇((B◇(B◇B))◇q0))=q2:=(K (K rfl (K rfl (K rfl (S (l3 B B B))))) rfl).symm.trans r5
  have r7:((B◇(B◇(B◇B)))◇((B◇(B◇B))◇q0))=q2:=(K (l96 B B B) rfl).symm.trans r6
  have r8:((B◇(B◇(B◇B)))◇((B◇(B◇B))◇q1))=q2:=(K rfl (K rfl (l98 B B))).symm.trans r7
  have r9:((B◇(B◇(B◇B)))◇B)=q2:=(K rfl (l40 B B)).symm.trans r8
  have r10:(B◇B)=q2:=(S (l99 B B)).trans r9
  have r11:(B◇B)=(q1◇((B◇(B◇B))◇q0)):=r10.trans (K (l98 B B) rfl)
  have r12:(B◇B)=(q1◇((B◇(B◇B))◇q1)):=r11.trans (K rfl (K rfl (l98 B B)))
  have r13:(B◇B)=(q1◇B):=r12.trans (K rfl (l40 B B))
  S r13
 let l102:=fun (B:G)=>
  let q0:G:=((B◇(B◇B))◇(B◇(B◇(B◇B))))
  let q1:G:=(B◇(B◇(B◇(B◇B))))
  let q2:G:=(q0◇((B◇(B◇B))◇q0))
  let q3:G:=(q1◇((B◇(B◇B))◇q1))
  let q4:G:=(q1◇((B◇(B◇B))◇q0))
  have r0:(q2◇((B◇(B◇B))◇q0))=q2:=l100 B
  have r1:(q4◇((B◇(B◇B))◇q0))=q2:=(K (K (l98 B B) rfl) rfl).symm.trans r0
  have r2:(q3◇((B◇(B◇B))◇q0))=q2:=(K (K rfl (K rfl (l98 B B))) rfl).symm.trans r1
  have r3:((q1◇B)◇((B◇(B◇B))◇q0))=q2:=(K (K rfl (l40 B B)) rfl).symm.trans r2
  have r4:((q1◇B)◇((B◇(B◇B))◇q1))=q2:=(K rfl (K rfl (l98 B B))).symm.trans r3
  have r5:((q1◇B)◇B)=q2:=(K rfl (l40 B B)).symm.trans r4
  have r6:((q1◇B)◇B)=q4:=r5.trans (K (l98 B B) rfl)
  have r7:((q1◇B)◇B)=q3:=r6.trans (K rfl (K rfl (l98 B B)))
  have r8:((q1◇B)◇B)=(q1◇B):=r7.trans (K rfl (l40 B B))
  have r9:((B◇B)◇B)=(q1◇B):=(K (l101 B) rfl).symm.trans r8
  have r10:((B◇B)◇B)=(B◇B):=r9.trans (l101 B)
  r10
 let l103:=fun (B C:G)=>
  calc ((B◇(B◇(C◇(B◇B))))◇(B◇B))
   _=((B◇(B◇(C◇((B◇B)◇B))))◇(B◇B)):=K (K rfl (K rfl (K rfl (S (l102 B))))) rfl
   _=(B◇(B◇B)):=l26 B C
 let l105:=fun (B C:G)=>
  let q0:G:=(B◇(B◇(C◇(B◇B))))
  calc (q0◇(B◇(B◇B)))
   _=(q0◇(q0◇(B◇B))):=K rfl (S (l103 B C))
   _=(B◇(C◇(B◇B))):=l96 B C B
 let l107:=fun (B C:G)=>
  let q0:G:=(B◇(B◇(C◇(B◇B))))
  calc ((B◇B)◇((B◇B)◇(B◇(C◇(B◇B)))))
   _=((B◇B)◇((B◇B)◇(q0◇(B◇(B◇B))))):=K rfl (K rfl (S (l105 B C)))
   _=B:=l43 B (q0)
 let l109:=fun (B C:G)=>
  calc (B◇C)
   _=(B◇((C◇C)◇((C◇C)◇(C◇(B◇(C◇C)))))):=K rfl (S (l107 C B))
   _=(C◇C):=(l3 ((C◇C)) B C).symm
 calc (x◇y)
  _=(y◇y):=l109 x y
  _=((x◇z)◇y):=(l109 (x◇z) y).symm
def submission:Goal:=submission.bridge

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4922_to_381 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4922_to_381
