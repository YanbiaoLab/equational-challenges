-- Equation1431 → Equation18745
-- Recorded verdict: false
-- Premise: x = (x ◇ x) ◇ (y ◇ (x ◇ x))
-- Conclusion: x = (x ◇ x) ◇ ((y ◇ x) ◇ (y ◇ x))
-- Original submission SHA-256: 8c728965d00b5c36948e60c471120a00d5c35dd71688cc991c27edd4af6443f4
-- Aurora-accepted correction SHA-256: 146d34b798827b5bb4f647110d6cc042e6a027a41cc0e4a7604fcfdfcecd3baa
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ x) ◇ (y ◇ (x ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ x) ◇ ((y ◇ x) ◇ (y ◇ x))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                     
set_option maxHeartbeats 1000000
namespace submission
inductive A where
  | e : A
  | k : A → A
  | p : A → A → A
namespace A
def L : A → A | e => e | k _ => e | p a _ => a
def R : A → A | e => e | k _ => e | p _ b => b
def U : A → A | e => e | k a => a | p _ _ => e
def s : A → Nat
  | e => 0
  | k a => s a + 1
  | p a b => (s a + 1) + (s b + 1)
abbrev N (a b : Nat) : Nat := (a + 1) + (b + 1)
inductive C : A → A → A → Prop
  | c0 (v00 v01 : A) (down : 2 * s v00 + 2 ≤ s (p v00 v00)) : C (p v00 v00) (p v01 (p v00 v00)) v00
  | c1 (v10 : A) (down : 2 * s (p v10 v10) + 2 ≤ s (p (p v10 v10) (p v10 v10))) : C (p (p v10 v10) (p v10 v10)) v10 (p v10 v10)
theorem C.r0 (v00 v01 : A) : C (p v00 v00) (p v01 (p v00 v00)) v00 :=
  .c0 v00 v01 (by change 2 * (s v00) + 2 ≤ N (s v00) (s v00); simp [N]; omega)
theorem C.r1 (v10 : A) : C (p (p v10 v10) (p v10 v10)) v10 (p v10 v10) :=
  .c1 v10 (by change 2 * (N (s v10) (s v10)) + 2 ≤ N (N (s v10) (s v10)) (N (s v10) (s v10)); simp [N]; omega)
def D (a b o : A) : Prop := (∃ v00 v01, a = (p v00 v00) ∧ b = (p v01 (p v00 v00)) ∧ o = v00) ∨ (∃ v10, a = (p (p v10 v10) (p v10 v10)) ∧ b = v10 ∧ o = (p v10 v10))
theorem code_cases {a b o : A} (h : C a b o) : D a b o := by
  unfold D
  cases h with
  | c0 => exact (fun h => Or.inl h) ⟨_, _, rfl, rfl, rfl⟩
  | c1 => exact (fun h => Or.inr (h)) ⟨_, rfl, rfl, rfl⟩
theorem ct {a a' b b' o : A} (ha : a = a') (hb : b = b') (h : C a' b' o) : C a b o := by
  cases ha; cases hb; exact h
def g (a b : A) : A := (R a)
theorem cg {a b o : A} (h : C a b o) : g a b = o := by cases h <;> rfl
theorem code_bounds {a b o : A} (h : C a b o) : 2 * s o + 2 ≤ s a := by
  cases h <;> assumption
noncomputable def v (a b : A) : A := by
  classical
  exact if ∃ o, C a b o then g a b else p a b
theorem v_hit {a b o : A} (h : C a b o) : v a b = o := by
  rw [v, if_pos ⟨o, h⟩]
  exact cg h
theorem v_raw {a b : A} (h : ¬ ∃ o, C a b o) : v a b = p a b := by simp [v, h]

theorem ec (a b : A) :
    (¬ ∃ o, C a b o) ∧ v a b = p a b ∨
    ∃ o, C a b o ∧ v a b = o ∧ 2 * s o + 2 ≤ s a := by
  by_cases h : ∃ o, C a b o
  · rcases h with ⟨o, hc⟩
    right; refine ⟨o, hc, v_hit hc, ?_⟩
    have q := code_bounds hc
    exact q
  · exact Or.inl ⟨h, v_raw h⟩
theorem t0 {a b : A} (h : a = b) : s a = s b := congrArg (fun q => s q) h
theorem t1 {a b : A} (h : a = b) : s (L a) = s (L b) := congrArg (fun q => s (L q)) h
theorem t2 {a b : A} (h : a = b) : s (R a) = s (R b) := congrArg (fun q => s (R q)) h
theorem n0 {w0 a : A} (h : a = (p w0 w0)) : s a = N (s w0) (s w0) := t0 h
theorem n2 {w0 a : A} (h : a = (p w0 w0)) : s (R a) = s w0 := t2 h
theorem n6 {w0 w1 a : A} (h : a = (p w0 (p w1 w1))) : s a = N (s w0) (N (s w1) (s w1)) := t0 h
theorem n7 {w0 a : A} (h : a = w0) : s a = s w0 := t0 h
theorem n8 {w0 a : A} (h : a = (p (p w0 w0) (p w0 w0))) : s a = N (N (s w0) (s w0)) (N (s w0) (s w0)) := t0 h
theorem n9 {w0 a : A} (h : a = (p (p w0 w0) (p w0 w0))) : s (R a) = N (s w0) (s w0) := t2 h
theorem sh (x y : A) : x = (v (v x x) (v y (v x x))) := by
  classical
  have B0 := ec x x
  have B1 := ec x x
  have B2 := ec y (v x x)
  have B3 := ec (v x x) (v y (v x x))
  rcases B0 with B0 | B0
  · have zr0_0 := n0 (B0.2)
    have zr0_1 : _ = s x := t1 (B0.2)
    have zr0_2 := n2 (B0.2)
    rcases B1 with B1 | B1
    · have zr1_0 := n0 (B1.2)
      have zr1_1 : _ = s x := t1 (B1.2)
      have zr1_2 := n2 (B1.2)
      rcases B2 with B2 | B2
      · have zr2_0 : _ = N (s y) (s (v x x)) := t0 (B2.2)
        have zr2_1 : _ = s y := t1 (B2.2)
        have zr2_2 : _ = s (v x x) := t2 (B2.2)
        rcases B3 with B3 | B3
        · have ha3 : (v x x) = (p x x) := B0.2
          have hb3 : (v y (v x x)) = (p y (p x x)) := (B2.2).trans ((congrArg (fun zzq => (p zzq (v x x))) (rfl)).trans (congrArg (fun zzq => (p y zzq)) (B0.2)))
          exact (B3.1 (Exists.intro x (ct ha3 hb3 (C.r0 x y)))).elim
        · rcases B3 with ⟨o3, h3, e3, l3⟩
          have cg3 := cg h3
          have cx : g (v x x) (v y (v x x)) = x := by
            change (R (v x x)) = x
            calc
              (R (v x x)) = (R (p x x)) := congrArg (fun q => (R q)) (B0.2)
              _ = x := rfl
          exact cx.symm.trans (cg3.trans e3.symm)
      · rcases B2 with ⟨o2, h2, e2, l2⟩
        have s2 := code_cases h2
        rcases s2 with (⟨q200, q201, a20, b20, c20⟩ | ⟨q210, a21, b21, c21⟩)
        · have a20_0 := n0 (a20)
          have a20_2 := n2 (a20)
          have b20_0 := n6 (b20)
          have c20_0 := n7 (c20)
          have e20_0 := n7 (e2.trans c20)
          rcases B3 with B3 | B3
          · have ha3 : (v x x) = (p (p q200 q200) (p q200 q200)) := (B0.2).trans ((congrArg (fun zzq => (p zzq x)) ((((congrArg (fun q => (R q)) (b20)).symm).trans (congrArg (fun q => (R q)) (B0.2))).symm)).trans (congrArg (fun zzq => (p (p q200 q200) zzq)) ((((congrArg (fun q => (R q)) (b20)).symm).trans (congrArg (fun q => (R q)) (B0.2))).symm)))
            have hb3 : (v y (v x x)) = q200 := e2.trans c20
            exact (B3.1 (Exists.intro (p q200 q200) (ct ha3 hb3 (C.r1 q200)))).elim
          · rcases B3 with ⟨o3, h3, e3, l3⟩
            have cg3 := cg h3
            have cx : g (v x x) (v y (v x x)) = x := by
              change (R (v x x)) = x
              calc
                (R (v x x)) = (R (p x x)) := congrArg (fun q => (R q)) (B0.2)
                _ = x := rfl
            exact cx.symm.trans (cg3.trans e3.symm)
        · have a21_0 := n8 (a21)
          have a21_4 := n9 (a21)
          have b21_0 := n7 (b21)
          have c21_0 := n0 (c21)
          have e21_0 := n0 (e2.trans c21)
          rcases B3 with B3 | B3
          · have ha3 : (v x x) = (p x x) := B0.2
            have hb3 : (v y (v x x)) = (p (p x x) (p x x)) := (e2.trans c21).trans ((congrArg (fun zzq => (p zzq q210)) (((congrArg (fun q => q) (b21)).symm).trans ((B0.2)))).trans (congrArg (fun zzq => (p (p x x) zzq)) (((congrArg (fun q => q) (b21)).symm).trans ((B0.2)))))
            exact (B3.1 (Exists.intro x (ct ha3 hb3 (C.r0 x (p x x))))).elim
          · rcases B3 with ⟨o3, h3, e3, l3⟩
            have cg3 := cg h3
            have cx : g (v x x) (v y (v x x)) = x := by
              change (R (v x x)) = x
              calc
                (R (v x x)) = (R (p x x)) := congrArg (fun q => (R q)) (B0.2)
                _ = x := rfl
            exact cx.symm.trans (cg3.trans e3.symm)
    · rcases B1 with ⟨o1, h1, e1, l1⟩
      have s1 := code_cases h1
      rcases s1 with (⟨q100, q101, a10, b10, c10⟩ | ⟨q110, a11, b11, c11⟩)
      · have a10_0 := n0 (a10)
        have a10_2 := n2 (a10)
        have b10_0 := n6 (b10)
        have b10_2 : _ = N (s q100) (s q100) := t2 (b10)
        have c10_0 := n7 (c10)
        have e10_0 := n7 (e1.trans c10)
        grind [L, R, U, s]
      · have a11_0 := n8 (a11)
        have a11_4 := n9 (a11)
        have b11_0 := n7 (b11)
        have c11_0 := n0 (c11)
        have e11_0 := n0 (e1.trans c11)
        grind [L, R, U, s]
  · rcases B0 with ⟨o0, h0, e0, l0⟩
    have s0 := code_cases h0
    rcases s0 with (⟨q000, q001, a00, b00, c00⟩ | ⟨q010, a01, b01, c01⟩)
    · have a00_0 := n0 (a00)
      have a00_2 := n2 (a00)
      have b00_0 := n6 (b00)
      have b00_2 : _ = N (s q000) (s q000) := t2 (b00)
      have c00_0 := n7 (c00)
      have e00_0 := n7 (e0.trans c00)
      grind [L, R, U, s]
    · have a01_0 := n8 (a01)
      have a01_4 := n9 (a01)
      have b01_0 := n7 (b01)
      have c01_0 := n0 (c01)
      have e01_0 := n0 (e0.trans c01)
      grind [L, R, U, s]
noncomputable instance instMagma2 : Magma A where op := v
theorem nt0 : ¬ ∃ o, C (A.k A.e) (A.k A.e) o := by
  rintro ⟨o, h⟩
  cases h
theorem nt1 : ¬ ∃ o, C A.e (A.k A.e) o := by
  rintro ⟨o, h⟩
  cases h
theorem nt3 : ¬ ∃ o, C (A.p A.e (A.k A.e)) (A.p A.e (A.k A.e)) o := by
  rintro ⟨o, h⟩
  cases h
theorem nt4 : ¬ ∃ o, C (A.p (A.k A.e) (A.k A.e)) (A.p (A.p A.e (A.k A.e)) (A.p A.e (A.k A.e))) o := by
  rintro ⟨o, h⟩
  cases h
end A
end submission
open submission
open submission.A
noncomputable def submission : Goal := by
  refine ⟨A, A.instMagma2, ?_, ?_⟩
  · intro x y
    exact A.sh x y
  · intro target
    have bad := target (A.k A.e) A.e
    have hl : (A.k A.e) = (A.k A.e) := rfl
    have hr : (v (v (A.k A.e) (A.k A.e)) (v (v A.e (A.k A.e)) (v A.e (A.k A.e)))) = (A.p (A.p (A.k A.e) (A.k A.e)) (A.p (A.p A.e (A.k A.e)) (A.p A.e (A.k A.e)))) := ((((congrArg (fun q => (v q (v (v A.e (A.k A.e)) (v A.e (A.k A.e))))) (v_raw nt0)).trans (congrArg (fun q => (v (A.p (A.k A.e) (A.k A.e)) (v q (v A.e (A.k A.e))))) (v_raw nt1))).trans (congrArg (fun q => (v (A.p (A.k A.e) (A.k A.e)) (v (A.p A.e (A.k A.e)) q))) (v_raw nt1))).trans (congrArg (fun q => (v (A.p (A.k A.e) (A.k A.e)) q)) (v_raw nt3))).trans ((v_raw nt4))
    have nb := hl.symm.trans (bad.trans hr)
    exact Bool.noConfusion (congrArg (fun q => match q with | e => false | k _ => false | p _ _ => true) nb)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1431_to_18745 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_1431_to_18745
