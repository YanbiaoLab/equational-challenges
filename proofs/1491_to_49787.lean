-- Equation1491 → Equation49787
-- Recorded verdict: false
-- Premise: x = (y ◇ x) ◇ (y ◇ (y ◇ x))
-- Conclusion: x ◇ y = (y ◇ (x ◇ (y ◇ x))) ◇ y
-- Original submission SHA-256: ec845465e5faf07f3bd8809c0158e977275085a36e0d168047fbee7e73c7aeb2
-- Aurora-accepted correction SHA-256: dd86e7b733c059de9c069eb16410609a550cf9902f875bcd0c8db50df6880b0b
-- Generator: equational-challenges standalone v2
-- All project definitions are embedded in this file.
import Mathlib

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ x) ◇ (y ◇ (y ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = (y ◇ (x ◇ (y ◇ x))) ◇ y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
              
namespace submission
open Finset Submodule Encodable Denumerable Cardinal Module
set_option maxHeartbeats 800000
theorem sN {G : Type*} [AddGroup G] (a b : G) : a - b = a + -b := sub_eq_add_neg a b
theorem aC {G : Type*} [AddCommSemigroup G] (a b : G) : a + b = b + a := add_comm a b
noncomputable section
abbrev A:=Π₀ _:ℕ,ℤ
instance:Free ℤ A:=inferInstance
structure qc where
 D:Finset A
 f:A→A
 I:Set.InjOn f D
 Z:0∈D
 J:f 0=0
 C:∀{a},a∈D→f a∈D→f (f a)-f a∈D
 V:∀{a},a∈D→f a∈D→f (f (f a)-f a)=a-f a
 S:∀{a b},a∈D→b∈D→a-f a=b-f b→a=b
 E:∀{a},a∈D→f a∉D→a-f a∉D
 Q:∀{a},a∈D→f a∉D→a-f a∉f '' D
namespace qc
def Im (f:qc):=f.D.image f.f
instance:Denumerable A:=
 ofEncodableOfInfinite A
attribute[-instance] instEncodableDFinsuppOfDecidableNeOfNat
lemma q5 (f:qc) (x:A): ∃y,∀(k:ℤ),k≠0→k•y∉span ℤ (f.D∪f.Im∪{x}:Set A):=by
 have zb:=rank_span_of_finset (R:=ℤ) (f.D∪f.Im∪{x}:Finset A)
 rw [coe_union,coe_union,coe_singleton] at zb
 have za:aleph0≤Module.rank ℤ A:=by
  rw [← (finsuppLequivDFinsupp ℤ).rank_eq]
  rw [rank_finsupp_self']
  exact aleph0_le_mk ℕ
 apply exists_smul_notMem_of_rank_lt (R:=ℤ)
 exact lt_of_lt_of_le zb za
@[irreducible]
def qf (f:qc) (x:A:=0):A:=
 Classical.choose (q5 f x)
lemma q0 (f:qc) (x:A) {k:ℤ} (hk:k≠0):
  k•f.qf x∉span ℤ (f.D∪f.Im∪{x}):=by
 rw [qf]
 exact Classical.choose_spec (q5 f x) k hk
lemma q2 (f:qc) (x:A):
  f.qf x∉span ℤ (f.D∪f.Im∪{x}):=by
 simpa using f.q0 x (one_ne_zero)
section
variable (f:qc) {x y:A} (a:A:=0)
lemma q3:f.qf a∉f.D:=by
 have hf:=f.q2 a
 contrapose! hf
 rw [mem_span_set']
 use 1,λ _ => 1,λ _ => ⟨f.qf a,by simp [hf]⟩
 simp
lemma q15 (hx:x∈f.D) (hy:y∈f.D) (h i j k l m:ℤ:=0) (hh:h≠0:=by decide):
  h•f.qf a≠i•a+j•x+k•y+l•f.f x+m•f.f y:=by
 have hf:=f.q0 a hh
 contrapose! hf
 rw [mem_span_set']
 use 5
 use λ n => if n=0 then i else if n=1 then j else if n=2 then k
  else if n=3 then l else m
 use λ n =>
  if n=0 then ⟨a,by simp⟩
  else if n=1 then ⟨x,by simp [hx]⟩
  else if n=2 then ⟨y,by simp [hy]⟩
  else if n=3 then ⟨f.f x,by simp [show f.f x∈f.Im by simp [Im]; use x]⟩
  else ⟨f.f y,by simp [show f.f y∈f.Im by simp [Im]; use y]⟩
 simp [hf,Fin.sum_univ_def,List.finRange_succ]
 abel
lemma qa (hx:x∈f.D) (hy:y∈f.D)
  (h1 i1 j1 k1 l1 m1 h2 i2 j2 k2 l2 m2:ℤ:=0) (hh:h1≠h2:=by decide):
 h1•f.qf a+i1•a+j1•x+k1•y+l1•f.f x+m1•f.f y≠
 h2•f.qf a+i2•a+j2•x+k2•y+l2•f.f x+m2•f.f y:=by
 have hf:=(f.q15 a hx hy (h2-h1) (i1-i2) (j1-j2) (k1-k2) (l1-l2) (m1-m2)
  (sub_ne_zero_of_ne hh.symm)).symm
 contrapose! hf
 rw [← neg_add_eq_zero] at hf ⊢
 rw [← hf,← neg_add_eq_zero]
 simp [sub_smul]
 abel
lemma q1c (hx:x∈f.D):f.qf a≠f.f x:=by
 simpa using f.q15 a hx f.Z 1 0 0 0 1
lemma q10 (hx:x∈f.D) (hy:y∈f.D):f.qf a≠x+f.f y:=by
 simpa using f.q15 a hx hy 1 0 1 0 0 1
end
def q27 (f:qc) {x:A} (hx:x∈f.D):qc:=
 if hb:f.f x∈f.D then f else
  let b:=f.f x;
  let c:=f.qf;
  have hb:b∉f.D:=hb
  have x0:x≠0:=λ h => hb (h ▸ f.J.symm ▸ f.Z:f.f x∈f.D)
  have b0:b≠0:=λ h => hb (h ▸ f.Z)
  have hbx:b≠x:=λ h => hb (h ▸ hx)
  have hccb:c≠c-b:=λ h => b0 (sub_eq_self.mp h.symm)
  have yb:c≠c-x:=λ h => x0 (sub_eq_self.mp h.symm)
  have yc:x-b≠b:=
   have:∀z∈f.D,f.f z≠x-b:=by simpa using f.Q hx hb
   (this x hx).symm
  have hcd:c∉f.D:=f.q3
  have c0:c≠0:=by
   simpa using f.q15 _ f.Z f.Z 1
  have hbc:c≠b:=f.q1c _ hx
  have hcx:c≠x:=λ h => hcd (h ▸ hx)
  have yd:∀z∈f.D,c-z∉f.D:=λ z hz h =>
   (show _≠(c-z)+z by simpa+zetaDelta using f.q15 0 h hz 1 0 1 1)
    (eq_add_of_sub_eq rfl)
  have zw:∀z∈f.D,f.f z≠c-x:=λ z hz h =>
   f.q10 0 hx hz (add_eq_of_eq_sub' h).symm
  have ye:∀z∈f.D,c-z≠b:=λ _ hz h =>
   (f.q10 0 hz hx) (aC b _ ▸ eq_add_of_sub_eq h)
  have yf:b-c∉f.D:=λ h =>
   (show b-c≠b-c by
    simpa+zetaDelta [aC,← sN]
     using f.qa 0 hx h (-1) 0 0 0 1 0 0 0 0 1) rfl
  have zh:c-b≠b:=by
   simpa [← sN] using f.qa _ hx f.Z 1 0 0 0 (-1) 0 0 0 0 0 1
  have yg:c≠b-c:=by
   simpa [aC,← sN] using f.qa _ hx f.Z 1 0 0 0 0 0 (-1) 0 0 0 1
  have zx:b-c≠c-b:=by
   simpa+zetaDelta [aC _ b,← sN] using f.qa _ hx f.Z (-1) 0 0 0 1 0 1 0 0 0 (-1)
  have ze:∀z∈f.D,z≠c-b:=λ _ hz => by
   simpa [← sN] using f.qa _ hx hz 0 0 0 1 0 0 1 0 0 0 (-1)
  have zm:b-c≠c-b-(x-b):=by
   simpa+zetaDelta [aC _ b,← sN] using f.qa _ hx hx (-1) 0 0 0 1 0 1 0 0 (-1)
  have zt:∀z∈f.D,f.f z≠c-b:=λ z hz => by
   simpa [← sN] using f.qa _ hx hz 0 0 0 0 0 1 1 0 0 0 (-1)
  have zn:∀z∈f.D,c≠z-f.f z:=λ _ hz => by
   simpa [sN] using f.q15 _ hz f.Z 1 0 1 0 (-1)
  have zy:∀z∈f.D,f.f z≠b-c:=λ z hz => by
   simpa [aC,← sN] using f.qa _ hx hz 0 0 0 0 0 1 (-1) 0 0 0 1
  have zz:∀z∈f.D,z-b≠b-c:=λ z hz => by
   simpa+zetaDelta [aC _ b,← sN] using f.qa _ hx hz 0 0 0 1 (-1) 0 (-1) 0 0 0 1
  have ya:∀z∈f.D,z-b≠c-z:=λ z hz => by
   simpa [← sN] using f.qa _ hx hz 0 0 0 1 (-1) 0 1 0 0 (-1)
  have zu:∀z∈f.D,z-f.f z≠c-b:=λ z hz => by
   simpa [← sN] using f.qa _ hx hz 0 0 0 1 0 (-1) 1 0 0 0 (-1)
  have zq:∀z∈f.D,c-x≠z-f.f z:=λ z hz => by
   simpa [← sN] using f.qa _ hx hz 1 0 (-1) 0 0 0 0 0 0 1 0 (-1)
  have zr:∀z∈f.D,b-c≠z-f.f z:=λ z hz => by
   simpa+zetaDelta [aC _ b,← sN] using f.qa _ hx hz (-1) 0 0 0 1 0 0 0 0 1 0 (-1)
  have zs:∀z∈f.D,f.f z∈f.D→f.f (f.f z)-f.f z≠c-b:=λ z _ hfz => by
   simpa [aC (-f.f z),← sN] using f.qa _ hx hfz 0 0 0 (-1) 0 1 1 0 0 0 (-1)
  {
    D:=insert b <| insert (c-b) f.D
    f:=λ y =>
      if y=b then c
      else if y=c-b then x-b
      else f.f y
    I:=by
      intro y hy z hz
      simp at hy hz
      rcases hy with hy|hy|hy
     <;>rcases hz with hz|hz|hz
     <;>(try simp only [hy,hz,↓reduceIte,imp_self,zh])
     <;>(try have zg:y≠b:=λ h => hb (h ▸ hy); simp [zg])
     <;>(try have hzb:z≠b:=λ h => hb (h ▸ hz); simp [hzb])
     <;>(try simp only [ze y hy,↓reduceIte,not_false_eq_true,true_implies,imp_false,ne_eq])
     <;>(try simp only [ze z hz,↓reduceIte])
      · exact λ h => (zn x hx h).elim
      · exact λ h => (f.q1c _ hz h).elim
      · exact (zn x hx).symm
      · have:=by simpa using f.Q hx hb
        grind only
      · exact λ h => (f.q1c _ hy h.symm).elim
      · have:=by simpa using f.Q hx hb
        exact λ h => (this y hy h).elim
      · exact f.I hy hz
    Z:=by simp [f.Z]
    J:=by simpa [b0.symm,(sub_ne_zero_of_ne hbc).symm] using f.J
    C:=by
      intro y hy
      simp at hy
      rcases hy with rfl|rfl|hy
      · simp [hbc,hcd,hccb]
      · simpa+zetaDelta [zh,f.E hx hb,hcx.symm] using (by simp [·])
      · have zg:y≠b:=λ h => hb (h ▸ hy)
        simp [zg,ze y hy,zt y hy]
        rintro (zf|zi)
        · simp [zf]
        · have zf:f.f y≠b:=λ h => hb (h ▸ zi)
          have zo:f.f (f.f y)-f.f y≠b:=λ h => hb (h ▸ f.C hy zi)
          simp [zf,zo,zs y hy zi]
          exact f.C hy zi
    V:=by
      intro y hy
      simp at hy
      rcases hy with rfl|rfl|hy
      · simp [hbc,hcd,hccb]
      · simp+zetaDelta [zh,f.E hx hb,hcx.symm,yc]
      · have zg:y≠b:=λ h => hb (h ▸ hy)
        simp [zg,ze y hy,zt y hy]
        rintro (zf|zi)
        · simp [zf,zh]
          exact f.I hx hy zf.symm
        · have zf:f.f y≠b:=λ h => hb (h ▸ zi)
          have zo:f.f (f.f y)-f.f y≠b:=λ h => hb (h ▸ f.C hy zi)
          simp [zf,zo,zs y hy zi]
          exact f.V hy zi
    S:=by
      intro y z hy hz
      simp at hy hz
      rcases hy with hy|hy|hy
     <;>rcases hz with hz|hz|hz
     <;>(try simp only [hy,hz,↓reduceIte,imp_self,zh])
     <;>(try have zg:y≠b:=λ h => hb (h ▸ hy); simp [zg])
     <;>(try have hzb:z≠b:=λ h => hb (h ▸ hz); simp [hzb])
     <;>(try simp only [ze y hy,↓reduceIte,imp_false,ne_eq])
     <;>(try simp only [ze z hz,↓reduceIte])
      · exact λ h => (zm h).elim
      · exact λ h => (zr z hz h).elim
      · exact zm.symm
      · exact λ h => (zq z hz h).elim
      · exact (zr y hy).symm
      · exact (zq y hy).symm
      · exact f.S hy hz
    E:=by
      intro y hy
      simp at hy
      rcases hy with rfl|rfl|hy
      · simp [c0,zx,yf]
      · simp [zh,ye x hx,hbx.symm,yd x hx]
      · have zg:y≠b:=λ h => hb (h ▸ hy)
        simp [zg,ze y hy,zu y hy]
        intro _ _ h3
        constructor
        · intro h
          apply h ▸ f.Q hy h3
          use x,hx
        · exact f.E hy h3
    Q:=by
      intro y hy
      simp at hy
      rcases hy with rfl|rfl|hy
      · simp [yg,zh,zz x hx]
        intro _ _ _ y hy
        have zg:y≠b:=λ h => hb (h ▸ hy)
        simp [zg,ze y hy,zy y hy]
      · simp [zh,yb,ya x hx]
        intro _ _ _ y hy
        have zg:y≠b:=λ h => hb (h ▸ hy)
        simp [zg,ze y hy,zw y hy]
      · have zg:y≠b:=λ h => hb (h ▸ hy)
        simp [zg,ze y hy,zn y hy,zh]
        intro zf
        have hyx:y≠x:=λ h => zf (congrArg f.f h)
        have zv:x-b≠y-f.f y:=λ h => hyx.symm (f.S hx hy h)
        simp [zv]
        intro _ hy2 z hz
        have hzb:z≠b:=λ h => hb (h ▸ hz)
        have:=by simpa using f.Q hy hy2
        simpa [hzb,ze z hz] using this z hz
  }
lemma q1a (f:qc) {x:A} (hx:x∈f.D): ∀y∈f.D,y∈(f.q27 hx).D ∧ (f.q27 hx).f y=f.f y:=by
 intro y hy
 by_cases hf:f.f x∈f.D
 · simp [q27,hf,hy]
 · have h0:y≠f.f x:=λ e=>hf (e ▸ hy)
   have h:y≠f.qf-f.f x:=(f.q10 _ hy hx).symm ∘ add_eq_of_eq_sub
   simp [q27,hf,hy,h0,h]
lemma qd (f:qc) {x:A} (hx:x∈f.D): ∀y∈f.D,y∈(f.q27 hx).D:= λ y hy => ((f.q1a hx) y hy).1
lemma q13 (f:qc) {x:A} (hx:x∈f.D): ∀y∈f.D,(f.q27 hx).f y=f.f y:= λ y hy => ((f.q1a hx) y hy).2
lemma q1d (f:qc) {x:A} (hx:x∈f.D):
  (f.q27 hx).f x∈(f.q27 hx).D:=by
 by_cases hf:f.f x∈f.D
 · simp [q27,hf]
 · have h0:x≠f.f x:=λ e=>hf (e ▸ hx)
   have h:x≠f.qf-f.f x:=(f.q10 _ hx hx).symm ∘ add_eq_of_eq_sub
   simp [q27,hf,h0,h]
def add (f:qc) {x:A} (hx:x∉f.D) (zc:x∉f.Im)
    (zd:¬∃w,w∈f.D ∧ w-f.f w=x)
:qc:=
  have x0:x≠0:=λ h => hx (h ▸ f.Z:x∈f.D)
  let b:=f.qf x;
  have zp:b∉f.D:=f.q3 x
  have hxb:x-b∉f.D:=λ h =>
    (show x-f.qf x≠x-b
      by simpa [aC _ x,← sN] using f.qa x h f.Z (-1) 1 0 0 0 0 0 0 1 0 0) rfl
  have b0:b≠0:=by
    simpa using f.q15 x f.Z f.Z 1
  have hbx:b≠x:=by
    simpa using f.q15 x f.Z f.Z 1 1
  have hb2:∀z∈f.D,x-b≠z-f.f z:=λ _ hz => by
    simpa [aC,← sN] using f.qa x hz f.Z (-1) 1 0 0 0 0 0 0 1 0 (-1)
  have yh:b≠x-b:=by
    simpa [aC,← sN] using f.qa x f.Z f.Z 1 0 0 0 0 0 (-1) 1
  have hb3:∀z∈f.D,f.f z≠x-b:=λ _ hz => by
    simpa [aC,← sN] using f.qa x hz f.Z 0 0 0 0 1 0 (-1) 1
  have hb4:∀z∈f.D,b≠z-f.f z:=λ _ hz => by
    simpa [sN] using f.q15 x hz f.Z 1 0 1 0 (-1)
  {
    D:=insert x f.D
    f:=λ y => if x=y then b else f.f y
    I:=by
      intro y hy z hz
      simp only [coe_insert,Set.mem_insert_iff,mem_coe] at hy hz
      rcases hy with rfl|hy<;>rcases hz with rfl|hz
      · simp
      · have hyz:y≠z:=λ h => hx (h ▸ hz)
        simp only [hyz,↓reduceIte,imp_false,← ne_eq]
        symm
        exact (f.q1c y hz).symm
      · have hyz:y≠z:=λ h => hx (h ▸ hy)
        simp only [hyz.symm,hyz,↓reduceIte,imp_false,← ne_eq]
        exact (f.q1c z hy).symm
      · have zl:x≠y:=λ h => hx (h ▸ hy)
        have hxz:x≠z:=λ h => hx (h ▸ hz)
        simp only [zl,hxz,↓reduceIte]
        exact f.I hy hz
    Z:=by simp [f.Z]
    J:=by simp [x0,f.J]
    C:=by
      intro y hy
      rw [mem_insert] at hy
      rcases hy with rfl|hy
      · simp [hbx,zp]
      · have zl:x≠y:=λ h => hx (h ▸ hy)
        have zj:f.f y≠x:=λ h => zc (by simp [Im]; use y)
        simp only [zl,zj,zj.symm,false_or,↓reduceIte,mem_insert]
        exact λ h => Or.inr (f.C hy h)
    V:=by
      intro y hy
      rw [mem_insert] at hy
      rcases hy with rfl|hy
      · simp [hbx,zp]
      · have zl:x≠y:=λ h => hx (h ▸ hy)
        have zj:f.f y≠x:=λ h => zc (by simp [Im]; use y)
        simp only [zl,zj,zj.symm,false_or,↓reduceIte,mem_insert]
        intro hy2
        have zk:x≠f.f (f.f y)-f.f y:=λ h => hx (h ▸ f.C hy hy2)
        rw [if_neg zk]
        exact f.V hy hy2
    S:=by
      intro y z hy hz
      simp only [mem_insert,@eq_comm _ _ x] at hy hz
      rcases hy with rfl|hy<;>rcases hz with rfl|hz
      · simp
      · grind only
      · grind only
      · grind only [f.S]
    E:=by
      intro y hy
      simp only [mem_insert,@eq_comm _ _ x] at hy
      rcases hy with rfl|hy
      · simp [b0,hxb]
      · have zl:x≠y:=λ h => hx (h ▸ hy)
        simp only [zl,↓reduceIte,mem_insert,not_or,and_imp]
        intro _ h2
        have zj:y-f.f y≠x:=by
          simp only [not_exists,not_and] at zd
          exact zd y hy
        simpa [zj,not_false_eq_true,true_and] using f.E hy h2
    Q:=by
      intro y hy
      simp only [mem_insert,@eq_comm _ _ x] at hy
      rcases hy with rfl|hy
      · simp [zp,yh,hbx]
        intro z hz
        have hxz:x≠z:=λ h => hx (h ▸ hz)
        simp [hxz,hb3 z hz]
      · have zl:x≠y:=λ h => hx (h ▸ hy)
        simp [zl,hb4 y hy]
        intro _ h2 z hz
        have hxz:x≠z:=λ h => hx (h ▸ hz)
        have:=f.Q hy h2
        simp [hxz] at this ⊢
        exact this z hz
  }
lemma q23 (f:qc) {x:A} (hx:x∉f.D) (zc:x∉f.Im)
  (zd:¬∃w,w∈f.D ∧ w-f.f w=x): ∀y∈f.D,y∈(f.add hx zc zd).D ∧ (f.add hx zc zd).f y=f.f y:=by
 intro y hy
 have zl:x≠y:=λ h => hx (h ▸ hy)
 simp [add,hy,zl]
lemma q16 (f:qc) {x:A} (hx:x∉f.D) (zc:x∉f.Im)
  (zd:¬∃w,w∈f.D ∧ w-f.f w=x): ∀y∈f.D,y∈(f.add hx zc zd).D:= λ y hy => (f.q23 hx zc zd y hy).1
lemma q1e (f:qc) {x:A} (hx:x∉f.D) (zc:x∉f.Im)
  (zd:¬∃w,w∈f.D ∧ w-f.f w=x): ∀y∈f.D,(f.add hx zc zd).f y=f.f y:= λ y hy => (f.q23 hx zc zd y hy).2
lemma q25 (f:qc) {x:A} (hx:x∉f.D) (zc:x∉f.Im)
  (zd:¬∃w,w∈f.D ∧ w-f.f w=x):
  x∈(f.add hx zc zd).D:=by
 simp [add]
lemma q24.lem_1 {f:qc} {x:A} (zc:x∈f.Im): ∃! a,a∈f.D ∧ (λ x_1 => f.f x_1=x) a:=by
 obtain ⟨y,y1,y2⟩:=mem_image.mp zc;
 use y
 simp [y1,y2]
 exact λ _ hz => y2 ▸ (f.I hz y1)
lemma q24.lem_2 {f:qc} {x:A} (zc:x∈f.Im):
  let y:=choose (λ x_1 => f.f x_1=x) f.D (lem_1 zc);
  y∈f.D:=
 choose_mem _ _ _
lemma q24.lem_3 {f:qc} {x:A} (zc:x∈f.Im):
  let y:=choose (λ x_1 => f.f x_1=x) f.D (lem_1 zc);
  ∀(hy:y∈f.D:=lem_2 zc),x∈(f.q27 hy).D:=by
 intro y hy
 rw [← show (f.q27 hy).f y=x from (f.q13 _ _ hy).trans (choose_spec (f.f ·=x) _ _).2]
 exact f.q1d hy
def q24 (f:qc) (x:A) (zc:x∈f.Im):qc:=
  let y:A:=choose (f.f ·=x) f.D (q24.lem_1 zc)
  have hy:y∈f.D:=q24.lem_2 zc
  (f.q27 hy).q27 (q24.lem_3 zc hy)
lemma q28.lem_1 {f:qc} {x:A}
  (w0:∃! a,a∈f.D ∧ (λ w => w-f.f w=x) a):
  let w:=choose (λ w => w-f.f w=x) f.D w0;
  ∀(hw:w∈f.D),x∈(f.q27 hw).Im:=by
 intro w hw
 have w2:=f.qd hw _ hw
 simp only [Im,mem_image]
 use (f.q27 hw).f ((f.q27 hw).f w)-(f.q27 hw).f w
 constructor
 · exact (f.q27 hw).C w2 (f.q1d hw)
 · have wf:w-(f.q27 hw).f w=x:=(f.q13 _ w hw) ▸
   (choose_spec (λ w => w-f.f w=x) _ _).2
   rw [← wf]
   exact (f.q27 hw).V w2 (f.q1d hw)
def q28 (f:qc) (x:A):qc:=
 if hx:x∈f.D then
  f.q27 hx
 else if zc:x∈f.Im then
  f.q24 x zc
 else if zd:∃w,w∈f.D ∧ w-f.f w=x then
  let w:A:=choose (λ w => w-f.f w=x) f.D (by
   obtain ⟨y,y1,y2⟩:=zd;
   use y
   simp [y1,y2]
   exact λ _ hz => y2 ▸ (f.S hz y1)
  )
  have hw:w∈f.D:=choose_mem _ _ _
  (f.q27 hw).q24 x (q28.lem_1 _ _)
 else
  (f.add hx zc zd).q27 (f.q25 hx zc zd)
lemma q21 (f:qc) {x:A}:
  x∈(f.q28 x).D:=by
 rw [q28]
 split_ifs with h1 h2
 · apply qd
   exact h1
 · rw [q24]
   apply qd
   exact q24.lem_3 h2
 · rename_i h
   simp only [q24]
   apply qd
   exact q24.lem_3 (q28.lem_1 _ _)
 · apply qd
   apply q25
lemma q1b (f:qc) {x:A}:
  (f.q28 x).f x∈(f.q28 x).D:=by
 rw [q28]
 split_ifs
 · apply q1d
 · rw [q24]
   apply q1d
 · simp only [q24]
   apply q1d
 · apply q1d
lemma q1f (f:qc) (x:A): ∀y,y∈f.D→y∈(f.q28 x).D:=by
 rw [q28]
 split_ifs
 · apply qd
 · intro y hy
   rw [q24]
   apply qd
   apply qd _ _ _ hy
 · simp only [q24]
   intro y hy
   repeat apply qd
   exact hy
 · intro y hy
   apply qd
   exact q16 _ _ _ _ _ hy
lemma q17 (f:qc) (x:A): ∀y,y∈f.D→(f.q28 x).f y=f.f y:=by
 rw [q28]
 split_ifs
 · apply q13
 · intro y hy
   rw [q24,q13]
   apply q13 _ _ _ hy
   exact qd _ _ _ hy
 · simp only [q24]
   intro y hy
   repeat rw [q13 _ _ _]
   all_goals repeat apply qd
   all_goals assumption
 · intro y hy
   rw [q13]
   exact q1e _ _ _ _ _ hy
   exact q16 _ _ _ _ _ hy
def q20 (f:qc):ℕ→qc
| 0 =>f
| n+1 =>(q20 f n).q28 (ofNat A n)
lemma q11 (f:qc) (x:A):
  x∈(f.q20 (encode x+1)).D:=by
 rw [q20.eq_def]
 simp only [ofNat_encode _]
 apply q21
lemma qb (f:qc) (x:A):
  (f.q20 (encode x+1)).f x∈(f.q20 (encode x+1)).D:=by
 rw [q20.eq_def]
 simp only [ofNat_encode _]
 apply q1b
lemma qe (f:qc) (n:ℕ): ∀x,x∈f.D→x∈(f.q20 n).D:=by
 induction n
 · simp [q20]
 next k ih=>
  rw [q20]
  intro x hx
  apply (f.q20 k).q1f _ _ (ih x hx)
lemma q7 (f:qc) (n:ℕ): ∀x,x∈f.D→(f.q20 n).f x=f.f x:=by
 induction n
 · simp [q20]
 next k ih=>
  rw [q20]
  intro x hx
  rw [(f.q20 k).q17 _ x (f.qe _ _ hx)]
  exact ih x hx
lemma q8 (f:qc) (n k:ℕ): ∀x,x∈(f.q20 n).D→x∈(f.q20 (n+k)).D:=by
 induction k
 · simp
 next k ih=>
  intro x hx
  rw [← add_assoc,q20]
  exact (f.q20 _).q1f _ _ (ih x hx)
lemma q12 (f:qc) (n k:ℕ): ∀x,x∈(f.q20 n).D→(f.q20 (n+k)).f x=(f.q20 n).f x:=by
 induction k
 · simp
 next k ih=>
  intro x hx
  rw [← add_assoc,q20]
  rw [(f.q20 _).q17 _ x (f.q8 _ _ _ hx)]
  exact ih x hx
def q14 (f:qc):A→A:= λ a => (f.q20 (encode a+1)).f a
lemma q1 (f:qc) (n:ℕ) (a:A) (hn:a∈(q20 f n).D):
  f.q14 a=(f.q20 n).f a:=by
 simp only [q14]
 rcases le_total n (encode a+1) with h | h
 · obtain ⟨k,hk⟩:=Nat.le.dest h
   rw [← hk]
   exact q12 _ _ _ _ hn
 · obtain ⟨k,hk⟩:=Nat.le.dest h
   rw [← hk]
   symm
   apply q12
   apply q11
lemma q6 (f0:qc):
  let f:=q14 f0;
  ∀x,f (f (f x)-f x)=x-f x:=by
 dsimp
 intro x
 have x1:x∈(f0.q20 (encode x+1)).D:=
  f0.q11 x
 have x2:(f0.q20 (encode x+1)).f x∈(f0.q20 (encode x+1)).D:=
  f0.qb x
 rw [f0.q1 (encode x+1) x x1]
 rw [f0.q1 (encode x+1) _ x2]
 rw [f0.q1 (encode x+1)]
 · apply qc.V _ x1 x2
 · apply qc.C _ x1 x2
lemma q4 (f0:qc): ∀x,(h:x∈f0.D)→q14 f0 x=f0.f x:= λ x => q7 _ _ x
def q26 (f:qc):A→A→A:= λ a b => a+(q14 f) (b-a)
lemma q18 (f:qc):∀x y,
  x=q26 f (q26 f y x) (q26 f y (q26 f y x)):= λ x y => by simp [q26,q6 f (x-y)]
abbrev i:A:=fun₀ | 0 => 1
abbrev j:A:=fun₀ | 1 => 1
abbrev k:A:=fun₀ | 2 => 1
abbrev l:A:=fun₀ | 3 => 1
abbrev m:A:=fun₀ | 4 => 1
abbrev n:A:=fun₀ | 5 => 1
def p:qc where
 D:={0,-i,i,k-i,i+l,-m}
 f:=(fun₀ | -i => j | i => k | k-i => l | i+l => m | -m => n:DFinsupp _)
 I:=by
  intro x hx y hy
  simp only [coe_insert,coe_singleton] at hx hy
  rcases hx with (rfl|rfl|rfl|rfl|rfl|rfl)
 <;>rcases hy with (rfl|rfl|rfl|rfl|rfl|rfl)<;>decide
 Z:=by simp
 J:=by repeat rw [DFinsupp.coe_update,Function.update_of_ne]<;>decide
 C:=by decide
 V:=by decide
 S:=by
  intro a b
  simp only [mem_insert,mem_singleton]
  rintro (rfl|rfl|rfl|rfl|rfl|rfl)
 <;>rintro (rfl|rfl|rfl|rfl|rfl|rfl)<;>decide
 E:=by decide
 Q:=by
  intro
  simp only [mem_insert,mem_singleton,← coe_image]
  rintro (rfl|rfl|rfl|rfl|rfl|rfl)<;>decide
def z:Goal:=by
 use A,⟨p.q26⟩
 constructor
 · exact q18 p
 · simp only [EquationRHS,not_forall]
   use i,0
   change p.q26 i 0≠
   p.q26 (p.q26 0 (p.q26 i (p.q26 0 i))) 0
   simp [q26,p.q4 (-i) (by decide),show p.f (-i)=j by decide,q26,q26,q26,p.q4 i (by decide),show p.f i=k by decide,p.q4 (k-i) (by decide),show p.f (k-i)=l by decide,p.q4 (i+l) (by decide),show p.f (i+l)=m by decide,p.q4 (-m) (by decide),show p.f (-m)=n by decide]
   decide
end qc
end
end submission
def submission:=submission.qc.z

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1491_to_49787 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_1491_to_49787
