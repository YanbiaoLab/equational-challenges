-- Equation4158 → Equation3862
-- Recorded verdict: false
-- Premise: x ◇ y = ((y ◇ x) ◇ y) ◇ y
-- Conclusion: x ◇ x = (x ◇ (x ◇ x)) ◇ x
-- Original submission SHA-256: e4a084e7f2064f18d0750ce09043e133eb1c4c9feb579c71730cc53e918a558d
-- Aurora-accepted correction SHA-256: dc836e7d8f1488da3da37afe695a139dec3c310bd32c5003fe7c4a050f1143e6
-- Generator: equational-challenges standalone v2
-- All project definitions are embedded in this file.
import Mathlib.Tactic

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = ((y ◇ x) ◇ y) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x ◇ x = (x ◇ (x ◇ x)) ◇ x
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                     
set_option maxHeartbeats 0
namespace submission
noncomputable section
open Set Finset
abbrev I{α β}:α→α⊕β:=.inl
abbrev J{α β}:β→α⊕β:=.inr
namespace List
variable{α:Type*}
instance d{R:α→α→Prop}[DecidableRel R](l:List α):
 Decidable (_root_.List.IsChain R l):=by
 induction l with
 | nil=>exact .isTrue .nil
 | cons a as ih=>exact decidable_of_iff' _ List.isChain_cons
end List
theorem Exists.cr{α:Sort*}{p:α→Prop}(h:∃a,p a)
 {C:Sort*}(H:∀a,p a→C):∃a pa,h.classicalRecOn H=H a pa:=⟨_,_,rfl⟩
theorem ch{α β:Type*}[Preorder α][Countable β]
 (task:β→Set α) (H:∀a b,∃a',a≤a'∧a'∈task b) (a:α):∃c,IsChain (·≤·) c∧a∈c∧(∀x∈c,a≤x)∧∀b,∃a∈c,a∈task b:=by
 have⟨f,hf⟩:=exists_surjective_nat (Option β)
 let T:=Σ a',{c//a'∈c∧IsChain (·≤·) c∧∀ x∈c,a≤x∧x≤a'}
 let G:Nat→T→T:=fun n⟨a',c,ac,hc,hl⟩=>match f n with
 | none=>⟨a',c,ac,hc,hl⟩
 | some b=>by
   refine (H a' b).classicalRecOn fun a''⟨a'a'',_⟩=>?_
   refine⟨a'',insert a'' c,by simp,IsChain.insert hc ?_,?_⟩
   · exact fun d dc _=>.inr (le_trans (hl _ dc).2 a'a'')
   · refine Set.forall_mem_insert.2 ⟨⟨le_trans (hl _ ac).1 a'a'',le_rfl⟩,?_⟩
     exact fun d dc=>(hl _ dc).imp_right (le_trans · a'a'')
 let F:Nat→Σ a',{c//a'∈c∧IsChain (·≤·) c∧∀ x∈c,a≤x∧x≤a'}:=Nat.rec ⟨a,{a},rfl,Set.subsingleton_singleton.isChain,by simp⟩ G
 have hF i:F (i+1)=G i (F i):=rfl
 have:Monotone (fun i=>(F i).2.1):=monotone_nat_of_le_succ fun n=>by
  rw[hF];obtain⟨a',c,ac,hc,hl⟩:=F n
  simp only[G];split<;>simp only[le_refl]
  exact let⟨a,ha,eq⟩:=Exists.cr _ _;eq▸ by cases ha;simp
 refine⟨⋃ i,(F i).2.1,?_,?_,?_,fun b=>?_⟩
 · rintro a⟨_,⟨i,rfl⟩,hi⟩ b⟨_,⟨j,rfl⟩,hj⟩ ab;simp at hi hj⊢
   exact (F (max i j)).2.2.2.1 (this (le_max_left i j) hi) (this (le_max_right i j) hj) ab
 · refine⟨_,⟨0,rfl⟩,rfl⟩
 · rintro a'⟨_,⟨i,rfl⟩,h⟩;exact ((F i).2.2.2.2 _ h).1
 · clear_value F
   have⟨i,hi⟩:=hf (some b)
   specialize hF i;simp only[G] at hF
   revert hF;obtain⟨a',c,ac,hc,hl⟩:=F i;simp[hi]
   refine let⟨a,ha,eq⟩:=Exists.cr _ _;eq▸ ?_
   obtain⟨h1,h2⟩:=ha;simp;intro hF
   refine⟨a,⟨i+1,?_⟩,h2⟩
   rw[hF];simp
namespace J
universe u
variable{α:Type u}[Countable α]
private def e:ℕ≃ℕ⊕ α:=Classical.choice (inferInstance:Nonempty (ℕ≃ℕ⊕ α))
def adj(m:ℕ):ℕ≃ℕ⊕ α where
 toFun n:=if n<m then I n else match e (n-m) with
 | .inl k=>I (k+m)
 | .inr c=>J c
 invFun
 | .inl k=>if k<m then k else e.symm (I (k-m))+m
 | .inr c=>e.symm (J c)+m
 left_inv n:=by
  dsimp
  by_cases h:n<m
  · simp[h]
  · cases h':(e (α:=α) (n-m))<;>simp[h,h',I,J]<;>rw[←h']<;>simp<;>omega
 right_inv a:=by
  cases a
  case inl n=>simp only;by_cases h:n<m <;>simp[h] <;>omega
  case inr=>simp
end J
namespace M
abbrev P(α:Type):=α→α→Set α
abbrev V{α β:Type}(e:α≃β)(E:P β):P α:=fun a b=>{c|e c∈E (e a) (e b)}
class R where
 o:∀ {α:Type},P α→Prop
 e {α β:Type}(e:α≃β)(E:P β)(k:o E):o (V e E)
structure P.K[r:R]{α:Type}(E:P α):Prop where
 f:Set.Finite {x:(α×α)×α|x.2∈E x.1.1 x.1.2}
 g {x y}:Set.Subsingleton (E x y)
 o:R.o E
def K[R]{α β:Type}(e:α≃β)(E:P β)(k:E.K):
 (V e E).K where
  f:=by
   apply k.f.of_equiv
   constructor
   case toFun=>refine fun ⟨((a,b),c),h⟩=>⟨((e.symm a,e.symm b),e.symm c),by simpa⟩
   case invFun=>refine fun ⟨((a,b),c),h⟩=>⟨((e a,e b),e c),by simpa⟩
   case left_inv=>refine fun ⟨((a,b),c),h⟩=>?_;simp_all
   case right_inv=>refine fun ⟨((a,b),c),h⟩=>?_;simp_all
  g {x y} z hz z' hz':=by simpa using k.g hz hz'
  o:=R.e e E k.o
open R
abbrev T(α:Type) [R]:={E:P α//E.K}
class B[R] where
 E:P ℕ
 k:E.K
 a:ℕ
 b:ℕ
 ndf {c}:c∉E a b
namespace B
variable[R][B]
structure Z(F:Type)(E':P (ℕ⊕ F)):Prop where
 i {a b c}:c∈E a b→(I c)∈E' (I a) (I b)
 k:P.K E' (α:=(ℕ⊕ F))
 ab:(E' (I a) (I b)).Nonempty
abbrev Y(F:Type):={E':P (ℕ⊕ F)//Z F E'}
def m:Finset ℕ:=insert a<|insert b<|B.k.f.toFinset.biUnion fun ((a,b),c)=>{a,b,c}
theorem md{a b c x}
  (h1:c∈E a b) (h2:x∈({a,b,c}:Finset ℕ)):x∈m:=by
 refine mem_insert_of_mem<|mem_insert_of_mem ?_
 simp only[Finset.mem_biUnion,Set.Finite.mem_toFinset,mem_setOf_eq,Prod.exists]
 exact⟨_,_,_,h1,h2⟩
@[scoped aesop safe forward]
theorem dl{a b c}(h:c∈E a b):a∈m:=md h (by simp)
@[scoped aesop safe forward]
theorem dr{a b c}(h:c∈E a b):b∈m:=md h (by simp)
@[scoped aesop safe forward]
theorem dt{a b c}(h:c∈E a b):c∈m:=md h (by simp)
@[scoped aesop safe forward]
theorem da:a∈m:=mem_insert_self ..
@[scoped aesop safe forward]
theorem dbb:b∈m:=mem_insert_of_mem<|mem_insert_self ..
def db:=m.sup id+1
theorem ldb{x}(h:x∈m):x<db:=Nat.lt_succ_iff.2 (m.le_sup (f:=id) h)
namespace Y
variable {F:Type}[Countable F](E':Y F)
open J
def j:P ℕ:=V (adj db) E'.1
theorem ao:E'.j.K:=K (adj db) E'.1 E'.2.k
theorem al:E≤E'.j:=by
 intro a b c h
 unfold j V
 simp only[mem_setOf_eq]
 unfold adj
 simp only[Equiv.coe_fn_mk,ldb (dl h),↓reduceIte,ldb (dr h),ldb (dt h)]
 exact E'.2.i h
theorem aab:
 E'.j∈{e:(P ℕ)|Nonempty (e a b)}:=by
 obtain⟨c,c_mem⟩:=E'.2.ab
 use ((adj db).symm c)
 unfold j V
 simp only[mem_setOf_eq,Equiv.apply_symm_apply]
 unfold adj
 simp[ldb da,ldb dbb,c_mem]
end Y
end B
end M
namespace X
abbrev O(G:Type)[Magma G]:=∀x y:G,x◇y=x◇(x◇(y◇x))
namespace G
section
open J M B
abbrev F:=Fin 10
abbrev Rr(N:P (ℕ⊕F))(x y:ℕ):Prop:=(∃a,N (I x) (I y) (I a))∨∃b,N (I x) (I y) (J b)
structure L{α:Type}(E:P α):Prop where
  q{x y xy yx}:xy∈E x y→yx∈E y x→∃xyx∈E x yx,xy∈E x xyx
  l{x y z}:z∈E x y→x≠z
  r{x y z}:z∈E x y→y≠z
  c{x x' y xy}:xy∈E x y→xy∈E x' y→x=x'
  u{x y xy yxy}:xy∈E x y→yxy∈E y xy→∃yx,yx∈E y x
  u'{x y xy xyy}:xy∈E x y→xyy∈E xy y→∃yx,yx∈E y x
  w{x y w z}:z∈E x y→y∈E w z→y≠z→∃yx,yx∈E y x
def leq{α β:Type}(e:α≃β)(E:P β)(k:L E):L (V e E) where
  q p qh:=by obtain⟨xyx,uh,eq⟩:=k.q p qh;exact⟨e.symm xyx,by simpa using uh,by simpa using eq⟩
  l p h:=k.l p (by simpa using h)
  r p h:=k.r p (by simpa using h)
  c p p':=by simpa using k.c p p'
  u p rh:=by obtain⟨yx,qh⟩:=k.u p rh;exact⟨e.symm yx,by simpa using qh⟩
  u' p sh:=by obtain⟨yx,qh⟩:=k.u' p sh;exact⟨e.symm yx,by simpa using qh⟩
  w p th ineq:=by obtain⟨yx,qh⟩:=k.w p th (by simpa using ineq);exact⟨e.symm yx,by simpa using qh⟩
scoped instance:R where
 o:=L
 e:=leq
abbrev o[B]:=B.k.o
attribute[aesop safe forward]ndf
attribute[aesop safe forward]P.K.g
attribute[aesop safe forward]L.q
attribute[aesop safe forward]L.r
attribute[aesop safe forward]L.l
class A extends B where
  ea:b=a
namespace A
variable[A]
@[scoped aesop 50% [constructors]]
inductive N:ℕ⊕F→ℕ⊕F→ℕ⊕F→Prop
 | i {x y z}:z∈E x y→N (I x) (I y) (I z)
 | new:N (I a) (I a) (J 0)
 | e0:N (I a) (J 0) (J 1)
 | e1:N (I a) (J 1) (J 0)
 | e2:N (J 0) (I a) (J 2)
 | e3:N (I a) (J 2) (J 3)
 | e4:N (I a) (J 3) (J 1)
 | e5:N (J 0) (J 1) (J 4)
 | e6:N (J 0) (J 4) (J 2)
 | e7:N (J 1) (I a) (J 5)
 | e8:N (I a) (J 5) (J 6)
 | e9:N (I a) (J 6) (J 0)
 | e10:N (J 1) (J 0) (J 7)
 | e11:N (J 1) (J 7) (J 5)
 | e12:N (J 1) (J 4) (J 8)
 | e13:N (J 1) (J 8) (J 7)
 | e14:N (J 0) (J 7) (J 9)
 | e15:N (J 0) (J 9) (J 4)
theorem L{x y}:x∈E x y→False:=(o.l · rfl)
theorem R{x y}:y∈E x y→False:=(o.r · rfl)
theorem Y{x}(p:a∈E x a):Rr N a x:=(R p).elim
theorem U{x y z t}(p:z∈E x y)(q:t∈E y z):Rr N y x:=by obtain⟨u,h⟩:=o.u p q;exact .inl ⟨_,.i h⟩
theorem V{x y z t}(p:z∈E x y)(q:t∈E z y):Rr N y x:=by obtain⟨u,h⟩:=o.u' p q;exact .inl ⟨_,.i h⟩
theorem Q{x y z t}(p:z∈E x y)(q:t∈E y x):(∃a,N (I x) (I t) (I a)∧N (I x) (I a) (I z))∨∃b,N (I x) (I t) (J b)∧N (I x) (J b) (I z):=by obtain⟨u,h,k⟩:=o.q p q;exact .inl ⟨u,.i h,.i k⟩
theorem W{x y v z}(p:z∈E x y)(q:y∈E v z)(h:y≠z):Rr N y x:=by obtain⟨u,k⟩:=o.w p q h;exact .inl ⟨u,.i k⟩
@[scoped aesop safe destruct]
theorem Z{c}:c∉E a a:=ea▸ndf (c:=c)
theorem C{x x' y z}:N x y z→N x' y z→x=x':=by
 intro p q;cases p
 case i=>
  cases q<;>try rfl
  congr;apply o.c<;>assumption
 all_goals cases q<;>rfl
abbrev n:P (ℕ⊕F):=fun a b=>{c|N a b c}
def df:Finset (ℕ⊕F):=image (I) m∪image (J) univ
theorem no:n.K:={
  f:=by
    apply (finite_toSet ((df×ˢdf)×ˢdf)).subset
    refine fun ((x,y),z)h=>?_;unfold df;simp at h⊢
    cases h with
 | i h=>simp[dt h,dl h,dr h]
 | _=>simp[da]
  g:=by
    intro x y z h z' k
    cases h<;>cases k<;>try rfl
    case i.i _ _ _ h _ k=>congr;exact B.k.g h k
    all_goals exfalso;apply Z;assumption
  o:=by
    constructor<;>intros<;>simp only[n,mem_setOf_eq]at*
    case l=>cases_type* N<;>try aesop;all_goals exact L a
    case r=>cases_type* N<;>try aesop;all_goals exact R a
    case c=>exact C (by assumption) (by assumption)
    case q=>cases_type* N<;>try aesop;all_goals exact Q a a_1
    case u=>
      cases_type* N<;>try aesop
      all_goals first| exact U a a_1| skip
      all_goals exact Y a
    case u'=>
      cases_type* N<;>try aesop
      all_goals first| exact V a a_1| skip
      all_goals exact Y a
    case w=>cases_type* N<;>try aesop;all_goals exact W a a_2 a_1
    all_goals cases_type* N<;>try aesop
}
def ns:B.Z F N where
  i:=N.i
  k:=no
  ab:=⟨J 0,ea▸N.new⟩
end A
class C extends B where
  an:a≠b
  d:ℕ
  bd:d∈E b a
namespace C
variable[C]
@[scoped aesop safe forward]
theorem dd:d∈m:=dt bd
@[scoped aesop safe destruct]
theorem bn(h:b=a):False:=an h.symm
@[scoped aesop safe destruct]
theorem an'(h:a=b):False:=an h
@[scoped aesop safe destruct]
theorem dn(h:d=a):False:=o.r (h▸bd) rfl
@[scoped aesop safe destruct]
theorem ad(h:a=d):False:=o.r (h▸bd) rfl
@[scoped aesop safe destruct]
theorem dbn(h:d=b):False:=o.l (h▸bd) rfl
@[scoped aesop safe destruct]
theorem bdn(h:b=d):False:=o.l (h▸bd) rfl
@[scoped aesop safe destruct]
theorem az{x}(h:x∈E a d):False:=by
  obtain⟨x,ab⟩:=o.u bd h
  exact ndf ab
@[scoped aesop safe destruct]
theorem dz{x}(h:x∈E d a):False:=by
  obtain⟨x,ab⟩:=o.u' bd h
  exact ndf ab
@[scoped aesop 50% [constructors]]
inductive N:ℕ⊕F→ℕ⊕F→ℕ⊕F→Prop
 | i {x y z}:z∈E x y→N (I x) (I y) (I z)
 | new:N (I a) (I b) (J 0)
 | e0:N (I b) (J 0) (J 1)
 | e1:N (I b) (J 1) (I d)
 | e2:N (I a) (I d) (J 2)
 | e3:N (I a) (J 2) (J 0)
theorem H{x y}:(E y x).Nonempty→Rr N y x:=fun⟨z,h⟩=>.inl ⟨z,.i h⟩
abbrev n:P (ℕ⊕F):=fun a b=>{c|N a b c}
def df:Finset (ℕ⊕F):=image (I) m∪image (J) univ
theorem no:n.K:={
  f:=by
    apply (finite_toSet ((df×ˢdf)×ˢdf)).subset
    refine fun ((x,y),z) h=>?_;unfold df;simp at h ⊢
    cases h with
 | i h=>simp[dt h,dl h,dr h]
 | _=>simp[da,dbb,dd]
  g:=by
   intro x y z h z' k
   generalize e:x=u at k;generalize f:y=v at k
   cases h<;>cases k<;>aesop
   all_goals first|exfalso;apply ndf;assumption|apply B.k.g<;>assumption
  o:=by
   let O:L E:=o
   constructor<;>intros<;>simp only[n,mem_setOf_eq]at*<;>cases_type N
   all_goals try generalize ha:a=A at*;try generalize hb:b=B at*;try generalize hd:d=D at*
   all_goals try cases_type* N
   all_goals try subst A;try subst B;try subst D
   all_goals aesop
   all_goals try (exfalso;apply O.l<;>assumption)
   all_goals try (exfalso;apply O.r<;>assumption)
   all_goals try (apply O.c<;>assumption)
   all_goals try (apply H;apply O.u<;>assumption)
   all_goals try (apply H;apply O.u'<;>assumption)
   all_goals try (apply H;apply O.w<;>assumption)
   all_goals try (have:z=d:=B.k.g a bd;subst z;exact .inr ⟨1,.e0,.e1⟩)
   all_goals try (have:z=d:=B.k.g a bd;subst z;exact .inr ⟨2,.e2,.e3⟩)
   all_goals try (apply H;apply O.u'<;>first|assumption|exact bd)
   all_goals try (have:x=b:=O.c a bd;subst x;exact .inr ⟨0,.new⟩)
   all_goals try exact .inl ⟨d,.i bd⟩
   all_goals try (apply H;apply O.u<;>first|assumption|exact bd)
   all_goals try (apply H;apply O.w<;>first|assumption|exact bd|exact dn)
}
def ns:Z F N where
  i:=N.i
  k:=no
  ab:=⟨_,N.new⟩
end C
class D extends B where
  an:a≠b
  bz{d}:d∉E b a
  ai{d}:a∉E d b
  bi{d}:b∉E d a
namespace D
variable[D]
theorem bn(h:b=a):False:=an h.symm
theorem an'(h:a=b):False:=an h
inductive N:ℕ⊕F→ℕ⊕F→ℕ⊕F→Prop
 | i {x y z}:z∈E x y→N (I x) (I y) (I z)
 | new:N (I a) (I b) (J 0)
 | e0:N (I b) (J 0) (J 1)
 | e1:N (I b) (J 1) (J 2)
 | e2:N (I b) (I a) (J 2)
 | e3:N (I a) (J 2) (J 3)
 | e4:N (I a) (J 3) (J 0)
theorem H{x y}:(E y x).Nonempty→Rr N y x:=fun⟨z,h⟩=>.inl ⟨z,N.i h⟩
abbrev n:P (ℕ⊕F):=fun a b=>{c|N a b c}
def df:Finset (ℕ⊕F):=image I m∪image J univ
theorem no:n.K:={
  f:=by
    apply (finite_toSet ((df×ˢdf)×ˢdf)).subset
    refine fun ((x,y),z) h=>?_;unfold df;simp at h ⊢
    cases h with
 | i h=>simp[dt h,dl h,dr h]
 | _=>simp[da,dbb]
  g:=by
   intro x y z h z' k
   cases h<;>generalize e:a=A at*<;>generalize f:b=B at*<;>cases k
   case i.i _ _ _ h _ k=>congr;exact M.B.k.g h k
   all_goals try subst A;try subst B
   all_goals simp only[I,J,an,bn,bz,ndf]at*
  o:=by
   let O:L E:=o
   constructor<;>intros<;>simp only[n,mem_setOf_eq]at*<;>cases_type N
   all_goals try generalize e:a=A at*;try generalize f:b=B at*
   all_goals try cases_type* N
   all_goals try subst A;try subst B
   all_goals try simp only[I,J,bz,ai,bi,an,bn]at*
   all_goals try simp
   all_goals try (exfalso;exact ndf (by assumption))
   all_goals try exact .inr ⟨3,N.e3,N.e4⟩
   all_goals try exact .inr ⟨1,N.e0,N.e1⟩
   all_goals try exact .inr ⟨2,N.e2⟩
   all_goals try exact .inr ⟨0,f ▸ N.new⟩
   all_goals try exact Eq.symm (by assumption)
   all_goals try (first
    | exact O.l (by assumption)
    | exact O.r (by assumption)
    | exact O.c (by assumption) (by assumption))
   all_goals try (apply H;first|apply O.u<;>assumption|apply O.u'<;>assumption)
   case q.i.i _ _ _ p _ q=>obtain⟨u,h,k⟩:=O.q p q;exact .inl ⟨u,.i h,.i k⟩
   case w.i.i _ _ _ p ne _ q=>apply H;exact O.w p q fun e=>ne <|congrArg I e
 }
def ns:Z F N where
  i:=N.i
  k:=no
  ab:=⟨_,N.new⟩
end D
theorem v:∀(E:T ℕ)(a b:ℕ),(E.1 b a).Nonempty →
  ∃ E':T ℕ,E≤E'∧E'∈{e:T ℕ| (e.1 a b).Nonempty}:=fun ⟨E,k⟩ a b s=>by
  if h:(E a b).Nonempty then exact ⟨_,le_rfl,h⟩ else
  if ea:b=a then exact ⟨_,le_rfl,ea ▸ s⟩ else
    let d:=s.choose
    let bd:=s.choose_spec
    let E2:C:=
      { E,k,a,b,ndf:=(fun h'=>h ⟨_,h'⟩),an:=by tauto,d,bd }
    let Y:Y F:=⟨_,E2.ns⟩
    obtain ⟨⟨x,hx⟩⟩ := (@B.Y.aab _ E2.toB _ _ Y)
    exact ⟨⟨Y.j,Y.ao⟩,Y.al,⟨x,hx⟩⟩
theorem t:∀(E:T ℕ)(a b:ℕ),
  ∃ E':T ℕ,E≤E'∧E'∈{e:T ℕ| (e.1 a b).Nonempty}:=fun ⟨E,k⟩ a b=>by
  if h:(E a b).Nonempty then exact ⟨_,le_rfl,h⟩ else
  if ea:b=a then
    let E1:A:={ E,k,a,b,ndf:=(fun h'=>h ⟨_,h'⟩),ea }
    let Y:Y F:=⟨_,E1.ns⟩
    obtain ⟨⟨x,hx⟩⟩ := (@B.Y.aab _ E1.toB _ _ Y)
    exact ⟨⟨Y.j,Y.ao⟩,Y.al,⟨x,hx⟩⟩
  else if h':(E b a).Nonempty then
    apply v;assumption
  else if p:∃ x,a∈E x b then
    rcases p with ⟨x,s⟩
    obtain ⟨E',le,⟨y,bx_def⟩⟩:=v ⟨E,k⟩ b x ⟨a,s⟩
    obtain ⟨ba,bd,_⟩:=E'.2.o.q bx_def (le _ _ s)
    obtain ⟨E'',le',⟨z,hz⟩⟩:=v E' a b ⟨ba,bd⟩
    exact ⟨E'',le_trans le le',⟨z,hz⟩⟩
  else if p:∃ x,b∈E x a then
    rcases p with ⟨x,xa_def⟩
    obtain ⟨E',le,⟨y,ax_def⟩⟩:=v ⟨E,k⟩ a x ⟨b,xa_def⟩
    obtain ⟨z,hz,_⟩:=E'.2.o.q ax_def (le _ _ xa_def)
    exact ⟨E',le,⟨z,hz⟩⟩
  else
    let E3:D:=
    { E,k,a,b,ndf:=(fun h'=>h ⟨_,h'⟩),
      an:=by tauto,bz:=by tauto,ai:=by tauto,bi:=by tauto}
    let Y:Y F:=⟨_,E3.ns⟩
    obtain ⟨⟨x,hx⟩⟩ := (@B.Y.aab _ E3.toB _ _ Y)
    exact ⟨⟨Y.j,Y.ao⟩,Y.al,⟨x,hx⟩⟩
variable(e₀:T ℕ)
theorem tot :
    ∃ op:ℕ→ℕ→ℕ,
    (∀ x y,op x y= op x (op x (op y x))) ∧
    (∀ {x y z},z∈e₀.1 x y→z=op x y):=by
  classical
  have ⟨c,hc,h1,h2,h3⟩:=ch (a:=e₀)
    (task:=fun x:_×_=>{e| (e.1 x.1 x.2).Nonempty}) fun ⟨E,k⟩ ⟨a,b⟩=>by
      apply t
  simp only[Subtype.exists,Prod.forall] at h3
  choose f hf1 hf2 op hop using h3
  refine ⟨op,fun x y=>?_,fun {x y z} H=>?_⟩
  · let S:Finset _:={(x,y),(y,x),(x,op y x),(x,op x (op y x))}
    have ⟨⟨e,he⟩,le⟩:=hc.directed.finset_le (hι:=⟨⟨_,h1⟩⟩)
      (S.image fun (a,b)=>⟨⟨f a b,hf1 a b⟩,hf2 a b⟩)
    replace le a (ha:a∈S):=forall_mem_image.1 le ha _ _ (hop a.1 a.2)
    simp only[Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq,S] at le
    obtain ⟨xy,yx,xyx,xxyx⟩:=le
    obtain ⟨xyx',xyx'_def,eq⟩:=(e.2.o.q xy yx)
    exact e.2.g eq (e.2.g xyx'_def xyx ▸ xxyx)
  · exact (hf1 ..).g (h2 _ (hf2 x y) _ _ H) (hop ..)
def GM(_:T ℕ):=ℕ
instance(n):OfNat (GM e₀) n:=inferInstanceAs (OfNat Nat n)
instance im:Magma (GM e₀) where
  op:=(tot e₀).choose
theorem _root_.submission.X.M.T.q:O (GM e₀):=
  (tot e₀).choose_spec.1
theorem T.i:∀ {x y z:GM e₀},z∈e₀.1 x y→z=x ◇ y:=
  (tot e₀).choose_spec.2
def fl(s:List ((Nat×Nat)×Nat)):P ℕ:=fun a b=>{c|((a,b),c)∈s}
theorem fo{s:List ((Nat×ₗNat)×Nat)}
 (sorted:s.IsChain (fun a b=>a.1<b.1):=by decide)
 (q:∀a∈s,∀b∈s,a.1.1=b.1.2→a.1.2=b.1.1→∃c∈s,c.1.1=a.1.1∧c.1.2=b.2
 ∧∃d∈s,d.1.1=a.1.1∧d.1.2=c.2∧d.2=a.2:=by decide)
 (l:∀a∈s,a.1.1≠a.2:=by decide) (r:∀a∈s,a.1.2≠a.2:=by decide)
 (c:∀a∈s,∀b∈s,a.1.2=b.1.2→a.2=b.2→a.1.1=b.1.1:=by decide)
 (u:∀a∈s,∀b∈s,b.1.1=a.1.2→b.1.2=a.2→∃c∈s,a.1.1=c.1.2∧a.1.2=c.1.1:=by decide)
 (u':∀a∈s,∀b∈s,b.1.1=a.2→b.1.2=a.1.2→∃c∈s,a.1.1=c.1.2∧a.1.2=c.1.1:=by decide)
 (w:∀a∈s,∀b∈s,a.2=b.1.2→a.1.2=b.2→a.1.2≠b.1.2→∃c∈s,a.1.1=c.1.2∧a.1.2=c.1.1:=by decide):(fl s).K where
  f:=List.finite_toSet s
  g h1 _ h2:=Decidable.by_contra fun h=>
    have:IsTrans ((ℕ×ₗℕ)×ℕ) (·.1<·.1):=⟨fun _ _ _=>lt_trans⟩
    letI:Std.Symm (fun a b:((ℕ×ₗℕ)×ℕ)=>a.1≠b.1):=⟨fun _ _ h=>h.symm⟩
    (List.isChain_iff_pairwise.1 sorted)|>.imp (fun h=>h.ne)
     |>.forall h1 h2 (by rintro ⟨⟩;exact h rfl) rfl
  o:={
  q:=fun h1 h2=>by
    obtain⟨⟨⟨x,y⟩,xyx⟩,uh,e1,e2,
    ⟨⟨x',xyx'⟩,xy'⟩,xy'_mem,xy'_def1,xy'_def2,xy'_def3⟩:=q _ h1 _ h2 rfl rfl
    simp only at e1 e2 xy'_def1 xy'_def2 xy'_def3
    exists xyx
    use e2 ▸ e1 ▸ uh
    use xy'_def1 ▸ xy'_def2 ▸ xy'_def3 ▸ xy'_mem
  l:=l _
  r:=r _
  c:=fun h h'=>c _ h _ h' rfl rfl
  u:=fun h h'=>by
    obtain ⟨⟨⟨y,x⟩,yx⟩,qh,d1,d2⟩:=u _ h _ h' rfl rfl
    simp only at d1 d2
    exact ⟨yx,d1 ▸ d2 ▸ qh⟩
  u':=fun h h'=>by
    obtain ⟨⟨⟨y,x⟩,yx⟩,qh,d1,d2⟩:=u' _ h _ h' rfl rfl
    simp only at d1 d2
    exact ⟨yx,d1 ▸ d2 ▸ qh⟩
  w:=fun h h' ineq=>by
    obtain ⟨⟨⟨y,x⟩,yx⟩,qh,d1,d2⟩:=w _ h _ h' rfl rfl ineq
    simp only at d1 d2
    exact ⟨yx,d1 ▸ d2 ▸ qh⟩
}
theorem V{e:T ℕ}{s:List ((Nat×ₗNat)×Nat)}(hS:e.1=fl s)
 (a b c:Nat)(h:(toLex (a,b),c)∈s:=by decide):
 haveI:Magma Nat:=im e;a◇b=c:=
  (T.i e (hS ▸ h)).symm
end
end G
open G M
def z:List ((Nat×ₗNat)×Nat):=[((0,0),1),((0,1),3),((0,2),4),((0,3),1),((0,4),3),((1,0),2),((1,2),5),((1,3),5),((1,5),2),((2,1),5),((2,5),1),((3,0),4),((3,1),0),((3,4),0),((3,5),4),((4,0),3),((4,3),0),((5,1),2),((5,2),1)]
def e:M.T Nat:=⟨fl z,fo⟩
abbrev H:=GM e
def D:=H
instance(n):OfNat D n:=inferInstanceAs (OfNat H n)
instance j:Magma D where op x y:=@Magma.op H (im e) y x
theorem s:EquationLHS D:=by
  intro x y
  change @Magma.op H (im e) y x = @Magma.op H (im e) y (@Magma.op H (im e) y (@Magma.op H (im e) x y))
  exact M.T.q e (x:=y) (y:=x)
theorem t:¬EquationRHS D:=by
  intro h
  have t:=h (0:D)
  change @Magma.op H (im e) 0 0=@Magma.op H (im e) 0 (@Magma.op H (im e) (@Magma.op H (im e) 0 0) 0) at t
  rw[show @Magma.op H (im e) 0 0=1 from V rfl 0 0 1,
    show @Magma.op H (im e) 1 0=2 from V rfl 1 0 2,
    show @Magma.op H (im e) 0 2=4 from V rfl 0 2 4] at t
  have u:(1:Nat)=4:=t
  omega
end X
end
end submission
open submission.X
def submission:Goal:=⟨D,j,s,t⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4158_to_3862 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_4158_to_3862
