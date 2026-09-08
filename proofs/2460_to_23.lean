-- Equation2460 → Equation23
-- Recorded verdict: false
-- Premise: x = (x ◇ ((y ◇ x) ◇ y)) ◇ y
-- Conclusion: x = (x ◇ x) ◇ x
-- Original submission SHA-256: a5aa80e42eb93bef689316201b15d445f848e68e85995255a79450b6f9ce19d2
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Pairing

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ ((y ◇ x) ◇ y)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = (x ◇ x) ◇ x
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   
                     
set_option maxHeartbeats 4000000
namespace submission
open Finset
structure P where
 R:Nat→Nat→Nat→Prop
 
 r0:∀{x0 x1 x2 x3},R x0 x1 x2→R x0 x1 x3→x2=x3
 r1:∀{x0 x1 x2 x3 x4},R x0 x1 x2→R x1 x3 x4→R x2 x0 x3→R x4 x0 x1
 r2:∀{x0 x1 x2 x3},R x0 x0 x1→R x1 x0 x2→R x2 x0 x3→R x3 x0 x2
 s:Finset Nat
 m1:∀{x y z},R x y z→x∈s
 m2:∀{x y z},R x y z→y∈s
 m3:∀{x y z},R x y z→z∈s
namespace P
variable(p:P)(a b c:Nat)
attribute [local aesop safe forward] P.r0 P.r1 P.r2
inductive N:Nat→Nat→Nat→Prop
| i{x y z}:p.R x y z→N x y z
| n0:N a b c
| n1{v2 y}(k0:p.R y a v2)(k1:p.R v2 y b):N c y a
| n2{v1}(k0:p.R b b v1)(k1:p.R v1 b a):N c b a
theorem q0(h:∀z,¬p.R a b z)(d:c∉p.s)(e:c≠a)(f:c≠b):
 ∀{x0 x1 x2 x3},(h0:N p a b c x0 x1 x2)→(h1:N p a b c x0 x1 x3)→x2=x3:=by
 intro x0 x1 x2 x3 h0 h1
 have A:=h0;have B:=h1
 cases h0<;>cases h1
 all_goals try {exfalso;exact h _ ‹_›}
 all_goals try {exfalso;exact d (p.m1 ‹_›)}
 all_goals try {exfalso;exact d (p.m2 ‹_›)}
 all_goals try {exfalso;exact d (p.m3 ‹_›)}
 all_goals first | exact N.n0  | exact N.n1 ‹_› ‹_› | exact N.n2 ‹_› ‹_› | skip
 all_goals aesop
 all_goals first | exact N.n0  | exact N.n1 ‹_› ‹_› | exact N.n2 ‹_› ‹_› | skip
 all_goals first | exact N.i ‹_› | skip
attribute [local aesop safe forward] q0
theorem q1(h:∀z,¬p.R a b z)(d:c∉p.s)(e:c≠a)(f:c≠b):
 ∀{x0 x1 x2 x3 x4},(h0:N p a b c x0 x1 x2)→(h1:N p a b c x1 x3 x4)→(h2:N p a b c x2 x0 x3)→N p a b c x4 x0 x1:=by
 intro x0 x1 x2 x3 x4 h0 h1 h2
 have A:=h0;have B:=h1;have C:=h2
 cases h0<;>cases h1<;>cases h2
 all_goals try {exfalso;exact h _ ‹_›}
 all_goals try {exfalso;exact d (p.m1 ‹_›)}
 all_goals try {exfalso;exact d (p.m2 ‹_›)}
 all_goals try {exfalso;exact d (p.m3 ‹_›)}
 all_goals first | exact N.n0  | exact N.n1 ‹_› ‹_› | exact N.n2 ‹_› ‹_› | skip
 all_goals aesop
 all_goals first | exact N.n0  | exact N.n1 ‹_› ‹_› | exact N.n2 ‹_› ‹_› | skip
 all_goals first | exact N.i ‹_› | skip
attribute [local aesop safe forward] q1
theorem q2(h:∀z,¬p.R a b z)(d:c∉p.s)(e:c≠a)(f:c≠b):
 ∀{x0 x1 x2 x3},(h0:N p a b c x0 x0 x1)→(h1:N p a b c x1 x0 x2)→(h2:N p a b c x2 x0 x3)→N p a b c x3 x0 x2:=by
 intro x0 x1 x2 x3 h0 h1 h2
 have A:=h0;have B:=h1;have C:=h2
 cases h0<;>cases h1<;>cases h2
 all_goals try {exfalso;exact h _ ‹_›}
 all_goals try {exfalso;exact d (p.m1 ‹_›)}
 all_goals try {exfalso;exact d (p.m2 ‹_›)}
 all_goals try {exfalso;exact d (p.m3 ‹_›)}
 all_goals first | exact N.n0  | exact N.n1 ‹_› ‹_› | exact N.n2 ‹_› ‹_› | skip
 all_goals aesop
 all_goals first | exact N.n0  | exact N.n1 ‹_› ‹_› | exact N.n2 ‹_› ‹_› | skip
 all_goals first | exact N.i ‹_› | skip
attribute [local aesop safe forward] q2
def nx(h:∀z,¬p.R a b z)(d:c∉p.s)(e:c≠a)(f:c≠b):P where
 R:=N p a b c
 r0:=q0 p a b c h d e f
 r1:=q1 p a b c h d e f
 r2:=q2 p a b c h d e f
 s:=p.s∪{a,b,c}
 m1:=by
  intro x y z e;cases e
  all_goals try {have:=p.m1 ‹_›;simp_all}
  all_goals try {have:=p.m2 ‹_›;simp_all}
  all_goals try {have:=p.m3 ‹_›;simp_all}
  all_goals simp
 m2:=by
  intro x y z e;cases e
  all_goals try {have:=p.m1 ‹_›;simp_all}
  all_goals try {have:=p.m2 ‹_›;simp_all}
  all_goals try {have:=p.m3 ‹_›;simp_all}
  all_goals simp
 m3:=by
  intro x y z e;cases e
  all_goals try {have:=p.m1 ‹_›;simp_all}
  all_goals try {have:=p.m2 ‹_›;simp_all}
  all_goals try {have:=p.m3 ‹_›;simp_all}
  all_goals simp
def fr:Nat:=max (p.s.sup id) (max a b)+1
theorem fs:fr p a b∉p.s:=by intro q;have e:=p.s.le_sup (f:=id) q;dsimp[fr]at e;omega
theorem fa:fr p a b≠a:=by unfold fr;omega
theorem fb:fr p a b≠b:=by unfold fr;omega
open scoped Classical
noncomputable def ad:P:=if h:∃z,p.R a b z then p else nx p a b (fr p a b) (by simpa using h) (fs p a b) (fa p a b) (fb p a b)
theorem ah:∃z,(ad p a b).R a b z:=by
 unfold ad
 split
 case isTrue h=>exact h
 case isFalse=>exact⟨_,N.n0⟩
theorem ao{x y z}:p.R x y z→(ad p a b).R x y z:=by
 intro e
 unfold ad
 split
 case isTrue=>exact e
 case isFalse=>exact N.i e
noncomputable def sq:P→Nat→P|p,0=>p|p,n+1=>ad (sq p n) n.unpair.1 n.unpair.2
theorem mo1(p:P){i x y z}:(sq p i).R x y z→(sq p (i+1)).R x y z:=by change _→(ad (sq p i) _ _).R x y z;intro h;exact ao (sq p i) _ _ h
theorem mo(p:P){i j x y z}(ij:i≤j):(sq p i).R x y z→(sq p j).R x y z:=by intro h;induction ij with|refl=>exact h|@step j _ ih=>exact mo1 p ih
theorem st(p:P)(i:Nat):∃z,(sq p (i+1)).R i.unpair.1 i.unpair.2 z:=ah ..
def cp(p:P)(x y z:Nat):Prop:=∃i,(sq p i).R x y z
theorem ct(x y):∃z,cp p x y z:=by obtain⟨z,h⟩:=st p (Nat.pair x y);exact⟨z,_,by simpa using h⟩
theorem cf{x y z w}:cp p x y z→cp p x y w→z=w:=by rintro⟨i,h⟩⟨j,k⟩;let n:=max i j;exact (sq p n).r0 (mo p (Nat.le_max_left _ _) h) (mo p (Nat.le_max_right _ _) k)
theorem cb{x y z}:p.R x y z→cp p x y z:=fun h=>⟨0,h⟩
theorem cs(x0 x1 x2 x3 x4 : Nat):
 cp p x0 x1 x2→cp p x1 x3 x4→cp p x2 x0 x3→cp p x4 x0 x1:=by
 rintro ⟨i0,h0⟩ ⟨i1,h1⟩ ⟨i2,h2⟩
 let n:=max i2 (max i1 (max i0 (0)))
 exact⟨n,(sq p n).r1 (mo p (by omega) h0) (mo p (by omega) h1) (mo p (by omega) h2)⟩
noncomputable def op(x y:Nat):Nat:=(ct p x y).choose
theorem om(x y):cp p x y (op p x y):=(ct p x y).choose_spec
@[implicit_reducible]noncomputable def mag:Magma Nat:=⟨op p⟩
theorem lw:letI:=mag p;EquationLHS Nat:=by
 intro q0 q1
 exact cf p (cs p q1 q0 (op p q1 q0) (op p (op p q1 q0) q1) (op p q0 (op p (op p q1 q0) q1)) (om p q1 q0) (om p q0 (op p (op p q1 q0) q1)) (om p (op p q1 q0) q1)) (om p (op p q0 (op p (op p q1 q0) q1)) q1)
end P
def bs:P where
 R:=fun x y z=>(x,y,z)∈({(0, 0, 1),(1, 0, 1)}:Finset _)
 r0:=by simp_all only[mem_insert,mem_singleton,Prod.mk.injEq];aesop
 r1:=by simp_all only[mem_insert,mem_singleton,Prod.mk.injEq];aesop
 r2:=by simp_all only[mem_insert,mem_singleton,Prod.mk.injEq];aesop
 s:={0,1}
 m1:=by simp_all only[mem_insert,mem_singleton,Prod.mk.injEq];aesop
 m2:=by simp_all only[mem_insert,mem_singleton,Prod.mk.injEq];aesop
 m3:=by simp_all only[mem_insert,mem_singleton,Prod.mk.injEq];aesop
noncomputable instance mi:Magma Nat:=P.mag bs
theorem so:EquationLHS Nat:=P.lw bs
theorem e0:P.op bs 0 0=1:=P.cf bs (P.om bs 0 0) (P.cb bs (by unfold bs;decide))
theorem e1:P.op bs 1 0=1:=P.cf bs (P.om bs 1 0) (P.cb bs (by unfold bs;decide))
theorem co:¬EquationRHS Nat:=by
 intro h
 have q:=h 0
 change 0=(P.op bs (P.op bs 0 0) 0) at q
 simp only[e0,e1] at q <;> omega
end submission
def submission:Goal:=⟨Nat,submission.mi,submission.so,submission.co⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_2460_to_23 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_2460_to_23
