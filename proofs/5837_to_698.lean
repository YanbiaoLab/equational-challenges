-- Equation5837 → Equation698
-- Recorded verdict: false
-- Premise: x = y ◇ (x ◇ (y ◇ ((z ◇ y) ◇ y)))
-- Conclusion: x = y ◇ (x ◇ ((z ◇ w) ◇ x))
-- Original submission SHA-256: 4ad786aeb8ddcecc8f78218770ceff86c17729346e5f36dda13e3f601c750976
-- Aurora-accepted correction SHA-256: 9b599e7c28932a203b92f224ee4403a35e23747fcb032b9b47256f2093faca0f
-- Generator: equational-challenges standalone v2
-- All project definitions are embedded in this file.
import Lean

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (y ◇ ((z ◇ y) ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (x ◇ ((z ◇ w) ◇ x))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
           

namespace submission

set_option maxRecDepth 10000

inductive T where
  | e : T
  | E : T → T → T
  | M : T → T → T
  | R : T → T → T
deriving DecidableEq

namespace T

def sz : T → Nat
  | e => 0
  | E a b | M a b | R a b => sz a + sz b + 1

def owner : T → Option T
  | M o _ => some o
  | E q (E s t) =>
      if h : s = t then
        match owner s with
        | some o => if o = q then some (E s t) else none
        | none => none
      else none
  | _ => none

def cert : T → Option T
  | E s t => if s = t then owner s else none
  | _ => none

def afterJ (a b o : T) : T :=
  match a with
  | E q d => if b = E o o then M a q else R b a
  | _ => R b a

def afterA (a b : T) : T :=
  match owner a with
  | some o =>
      match b with
      | E o₁ (E o₂ t) =>
          if o₁ = o ∧ o₂ = o then M a t else afterJ a b o
      | _ => afterJ a b o
  | none => R b a

def afterG (a b : T) : T :=
  if a = E b b then M a b else afterA a b

def afterS (a b : T) : T :=
  match b with
  | R k p => if a = k then M a p else afterG a b
  | _ => afterG a b

def afterC (a b : T) : T :=
  match owner b with
  | some o => E o a
  | none => afterS a b

def afterD (a b : T) : T :=
  if a = b then
    match cert a with
    | some o => o
    | none => afterC a b
  else afterC a b

def op (a b : T) : T :=
  match b with
  | E k v => if a = k then v else afterD a b
  | _ => afterD a b

instance : Magma T where op := op

theorem owner_size {t o : T} (h : owner t = some o) : sz o < sz t := by
  cases t with
  | e => simp [owner] at h
  | M a p =>
      simp [owner] at h
      subst o
      simp [sz]
      omega
  | R a p => simp [owner] at h
  | E q d =>
      cases d with
      | e => simp [owner] at h
      | M a p => simp [owner] at h
      | R a p => simp [owner] at h
      | E s u =>
          by_cases hsu : s = u
          · subst u
            cases hs : owner s with
            | none => simp [owner, hs] at h
            | some r =>
                by_cases hrq : r = q
                · subst q
                  simp [owner, hs] at h
                  subst o
                  simp [sz]
                  omega
                · simp [owner, hs, hrq] at h
          · simp [owner, hsu] at h

theorem owner_ne_self (t : T) : owner t ≠ some t := by
  intro h
  exact (Nat.ne_of_lt (owner_size h)) rfl

theorem owner_asymm {a b : T} (h : owner a = some b) :
    owner b ≠ some a := by
  intro hba
  have hab := owner_size h
  have hba' := owner_size hba
  omega

theorem ne_E_left (a b : T) : a ≠ E a b := by
  intro h
  have hs := congrArg sz h
  simp [sz] at hs
  omega

theorem ne_E_right (a b : T) : b ≠ E a b := by
  intro h
  have hs := congrArg sz h
  simp [sz] at hs
  omega

theorem R_ne_left (a b : T) : R a b ≠ a := by
  intro h
  have hs := congrArg sz h
  simp [sz] at hs
  omega

theorem afterJ_fallback {a b o : T} (h : b ≠ E o o) :
    afterJ a b o = R b a := by
  cases a <;> simp [afterJ, h]

theorem afterA_double_fallback {a s o : T} (ha : owner a = some o)
    (hos : o ≠ s) : afterA a (E s s) = R (E s s) a := by
  have hJ : E s s ≠ E o o := by
    intro h
    injection h with hso
    exact hos hso.symm
  have hA : afterA a (E s s) = afterJ a (E s s) o := by
    rw [afterA, ha]
    cases s <;> simp_all
  rw [hA, afterJ_fallback hJ]

theorem op_self_cert {t o : T} (h : cert t = some o) : op t t = o := by
  cases t with
  | e => simp [cert] at h
  | M a b => simp [cert] at h
  | R a b => simp [cert] at h
  | E a b =>
      by_cases hab : a = b
      · subst b
        have hne : E a a ≠ a := by
          intro he
          have hs := congrArg sz he
          simp [sz] at hs
          omega
        simp [op, hne, afterD, h]
      · simp [cert, hab] at h

theorem double_none (o z : T) : owner (E o (E o z)) = none := by
  by_cases h : o = z
  · subst z
    cases ho : owner o with
    | none => simp [owner, ho]
    | some q =>
        have hqo : q ≠ o := by
          intro h
          subst q
          exact owner_ne_self o ho
        simp [owner, ho, hqo]
  · simp [owner, h]

theorem op_marker (o p x : T) : op x (M o p) = E o x := by
  by_cases h : x = M o p
  · subst x
    simp [op, afterD, cert, afterC, owner]
  · simp [op, afterD, afterC, owner, h]

theorem op_double {a o : T} (ha : owner a = some o) (z : T) :
    op a (E o (E o z)) = M a z := by
  have hao : a ≠ o := by
    intro h
    subst a
    exact owner_ne_self o ha
  have hab : a ≠ E o (E o z) := by
    intro h
    subst a
    rw [double_none] at ha
    contradiction
  have hoe : o ≠ E o z := by
    intro h
    have := congrArg sz h
    simp [sz] at this
    omega
  have hA : a ≠ E (E o (E o z)) (E o (E o z)) := by
    intro h
    subst a
    have hn : owner (E (E o (E o z)) (E o (E o z))) = none := by
      simp [owner, hoe]
    rw [hn] at ha
    contradiction
  simp [op, hao, hab, afterD, double_none, afterC, afterS, afterG,
    hA, afterA, ha]

theorem pOwner_marker (o p z : T) :
    owner (op (M o p) (op (op z (M o p)) (M o p))) = some (M o p) := by
  rw [op_marker, op_marker, op_double (by simp [owner])]
  simp [owner]

theorem op_child {s q : T} (hs : owner s = some q) (x : T)
    (hx : x ≠ q) : op x (E q (E s s)) = E (E s s) x := by
  have hqd : q ≠ E s s := by
    intro h
    have hlt := owner_size hs
    have he := congrArg sz h
    simp [sz] at he
    omega
  by_cases hxy : x = E q (E s s)
  · subst x
    simp [op, hx, afterD, cert, hqd, afterC, owner, hs]
  · simp [op, hx, afterD, afterC, owner, hs, hxy]

theorem sectionInv_marker (o p x : T) :
    op o (op x (M o p)) = x := by
  rw [op_marker]
  simp [op]

theorem sectionInv_child {s q : T} (hs : owner s = some q) (x : T) :
    op (E s s) (op x (E q (E s s))) = x := by
  by_cases hx : x = q
  · subst x
    rw [show op q (E q (E s s)) = E s s by simp [op]]
    exact op_self_cert (by simpa [cert] using hs)
  · rw [op_child hs x hx]
    simp [op]

theorem sectionInv {c o : T} (hc : owner c = some o) (x : T) :
    op o (op x c) = x := by
  cases c with
  | e => simp [owner] at hc
  | M a p =>
      simp [owner] at hc
      subst o
      exact sectionInv_marker a p x
  | R a p => simp [owner] at hc
  | E q d =>
      cases d with
      | e => simp [owner] at hc
      | M a p => simp [owner] at hc
      | R a p => simp [owner] at hc
      | E s t =>
          by_cases hst : s = t
          · subst t
            cases hs : owner s with
            | none => simp [owner, hs] at hc
            | some r =>
                by_cases hrq : r = q
                · subst q
                  simp [owner, hs] at hc
                  subst o
                  exact sectionInv_child hs x
                · simp [owner, hs, hrq] at hc
          · simp [owner, hst] at hc

theorem op_child_exception {s q : T} (hs : owner s = some q) :
    op (E q (E s s)) (E (E s s) (E s s)) = M (E q (E s s)) q := by
  let d := E s s
  let y := E q d
  have hlt := owner_size hs
  have hqd : q ≠ d := by
    intro h
    have he := congrArg sz h
    simp [d, sz] at he
    omega
  have hsd : s ≠ d := by
    intro h
    have he := congrArg sz h
    simp [d, sz] at he
    omega
  have hyr : y ≠ E d d := by
    intro h
    have he := congrArg sz h
    simp [y, d, sz] at he
    omega
  have hyd : y ≠ d := by
    intro h
    have he := congrArg sz h
    simp [y, d, sz] at he
    omega
  have hyA : y ≠ E (E d d) (E d d) := by
    intro h
    have he := congrArg sz h
    simp [y, d, sz] at he
    omega
  simp [y, d, op, hyd, afterD, hyr, afterC, owner, hs, hqd,
    afterS, afterG, hyA, afterA, hsd, afterJ]

theorem pOwner_child {s q : T} (hs : owner s = some q) (z : T) :
    owner (op (E q (E s s))
      (op (op z (E q (E s s))) (E q (E s s)))) =
      some (E q (E s s)) := by
  have hqd : q ≠ E s s := by
    intro h
    have hlt := owner_size hs
    have he := congrArg sz h
    simp [sz] at he
    omega
  by_cases hz : z = q
  · subst z
    rw [show op q (E q (E s s)) = E s s by simp [op]]
    rw [op_child hs (E s s) hqd.symm]
    rw [op_child_exception hs]
    simp [owner]
  · rw [op_child hs z hz]
    have hneq : E (E s s) z ≠ q := by
      intro h
      have he := congrArg sz h
      have hlt := owner_size hs
      simp [sz] at he
      omega
    rw [op_child hs _ hneq]
    rw [op_double (by simp [owner, hs])]
    simp [owner]

theorem diag_activation (z : T) : owner (op (E z z) z) = some (E z z) := by
  cases z with
  | e => simp [op, afterD, afterC, owner, afterS, afterG]
  | M a p => simp [op, afterD, afterC, owner]
  | R k p =>
      have hk : E (R k p) (R k p) ≠ k := by
        intro h
        have hs := congrArg sz h
        simp [sz] at hs
        omega
      simp [op, afterD, afterC, owner, afterS, hk, afterG]
  | E k v =>
      have hk : E (E k v) (E k v) ≠ k := by
        intro h
        have hs := congrArg sz h
        simp [sz] at hs
        omega
      have hself : E (E k v) (E k v) ≠ E k v :=
        (ne_E_left (E k v) (E k v)).symm
      cases hz : owner (E k v) <;>
        simp [op, hk, hself, afterD, afterC, hz, owner, afterS,
          afterG]

theorem op_cert_column {y o : T} (hy : owner y = none)
    (hc : cert y = some o) : op o y = R y o := by
  cases y with
  | e => simp [cert] at hc
  | M a b => simp [cert] at hc
  | R a b => simp [cert] at hc
  | E s t =>
      by_cases hst : s = t
      · subst t
        have hs : owner s = some o := by simpa [cert] using hc
        have hos : o ≠ s := by
          intro h
          subst o
          exact owner_ne_self s hs
        have hoy : o ≠ E s s := by
          intro h
          have hlt := owner_size hs
          have he := congrArg sz h
          simp [sz] at he
          omega
        have hbig : o ≠ E (E s s) (E s s) := by
          intro h
          have hlt := owner_size hs
          have he := congrArg sz h
          simp [sz] at he
          omega
        cases ho : owner o with
        | none =>
            simp [op, hos, afterD, hoy, afterC, hy, afterS, afterG,
              hbig, afterA, ho]
        | some r =>
            have hrs : r ≠ s := by
              intro h
              subst r
              exact owner_asymm hs ho
            simp only [op, hos, if_false, afterD, hoy, afterC, hy,
              afterS, afterG, hbig]
            exact afterA_double_fallback ho hrs
      · simp [cert, hst] at hc

theorem op_self_none (y : T) (hy : owner y = none)
    (hc : cert y = none) : op y y = R y y := by
  cases y with
  | e => simp [op, afterD, cert, afterC, afterS, afterG, afterA, owner]
  | M a b => simp [owner] at hy
  | E a b =>
      have hkey : E a b ≠ a := Ne.symm (ne_E_left a b)
      simp [op, hkey, afterD, hc, afterC, hy, afterS, afterG,
        ne_E_left, afterA]
  | R a b =>
      simp [op, afterD, hc, afterC, hy, afterS, R_ne_left,
        afterG, afterA]

theorem op_R_column {y r : T} (hy : owner y = none) :
    op (R y r) y = R y (R y r) := by
  cases y with
  | e => simp [op, afterD, afterC, afterS, afterG, afterA, owner]
  | M a b => simp [owner] at hy
  | E a b =>
      have hkey : R (E a b) r ≠ a := by
        intro h; have hs := congrArg sz h; simp [sz] at hs; omega
      simp [op, hkey, afterD, R_ne_left, afterC, hy, afterS,
        afterG, afterA, owner]
  | R a b =>
      have hkey : R (R a b) r ≠ a := by
        intro h; have hs := congrArg sz h; simp [sz] at hs; omega
      simp [op, afterD, R_ne_left, afterC, afterS, hkey,
        afterG, afterA, owner]

theorem owner_E_ne_left (k v : T) : owner (E k v) ≠ some k := by
  intro h
  cases v with
  | e => simp [owner] at h
  | M u w => simp [owner] at h
  | R u w => simp [owner] at h
  | E s t =>
      by_cases hst : s = t
      · subst t
        cases hs : owner s with
        | none => simp [owner, hs] at h
        | some o =>
            by_cases hok : o = k
            · subst o
              simp [owner, hs] at h
              have hlt := owner_size hs
              subst k
              simp [sz] at hlt
              omega
            · simp [owner, hs, hok] at h
      · simp [owner, hst] at h

theorem afterA_decode_column (k v : T) :
    afterA v (E k v) = R (E k v) v := by
  cases hv : owner v with
  | none => simp [afterA, hv]
  | some o =>
      have hJ : E k v ≠ E o o := by
        intro h
        injection h with hk hvo
        apply owner_ne_self v
        simpa only [← hvo] using hv
      cases v with
      | e => simpa [afterA, hv] using afterJ_fallback hJ
      | M u w => simpa [afterA, hv] using afterJ_fallback hJ
      | R u w => simpa [afterA, hv] using afterJ_fallback hJ
      | E u t =>
          by_cases hko : k = o
          · subst k
            by_cases huo : u = o
            · subst u
              exact False.elim ((owner_E_ne_left o t) hv)
            · simpa [afterA, hv, huo] using afterJ_fallback hJ
          · simpa [afterA, hv, hko] using afterJ_fallback hJ

theorem op_decode_column {k v : T} (hy : owner (E k v) = none)
    (hvk : v ≠ k) : op v (E k v) = R (E k v) v := by
  have hvself := ne_E_right k v
  have hbig : v ≠ E (E k v) (E k v) := by
    intro h; have hs := congrArg sz h; simp [sz] at hs; omega
  simp only [op, hvk, if_false, afterD, hvself, afterC, hy,
    afterS, afterG, hbig]
  exact afterA_decode_column k v

theorem afterJ_E_result {a k v o : T} (ha : owner a = some o) :
    afterJ a (E k v) o = R (E k v) a ∨
      ∃ r, afterJ a (E k v) o = M a r ∧ sz k < sz a := by
  cases a with
  | e => exact Or.inl rfl
  | M u w => exact Or.inl rfl
  | R u w => exact Or.inl rfl
  | E q d =>
      by_cases hJ : E k v = E o o
      · right
        refine ⟨q, by simp [afterJ, hJ], ?_⟩
        have hko : k = o := by
          injection hJ
        rw [hko]
        exact owner_size ha
      · left
        simp [afterJ, hJ]

theorem afterA_E_result {a k v o : T} (ha : owner a = some o) :
    afterA a (E k v) = R (E k v) a ∨
      ∃ r, afterA a (E k v) = M a r ∧ sz k < sz a := by
  simp only [afterA, ha]
  cases v with
  | e => exact afterJ_E_result ha
  | M u w => exact afterJ_E_result ha
  | R u w => exact afterJ_E_result ha
  | E u t =>
      by_cases hA : k = o ∧ u = o
      · right
        refine ⟨t, by simp [hA], ?_⟩
        rw [hA.1]
        exact owner_size ha
      · simpa [hA] using afterJ_E_result (a := a) (k := k)
          (v := E u t) ha

theorem afterA_e (a : T) : afterA a e = R e a := by
  cases ha : owner a with
  | none => simp [afterA, ha]
  | some o => cases a <;> simp [afterA, ha, afterJ]

theorem afterA_R (a k p : T) : afterA a (R k p) = R (R k p) a := by
  cases ha : owner a with
  | none => simp [afterA, ha]
  | some o => cases a <;> simp [afterA, ha, afterJ]

theorem op_M_E_column_of_lt {k v z r : T}
    (hy : owner (E k v) = none) (hlt : sz k < sz z) :
    op (M z r) (E k v) = R (E k v) (M z r) := by
  have hk : M z r ≠ k := by
    intro h; have hs := congrArg sz h; simp [sz] at hs; omega
  have hkz : k ≠ z := by
    intro h; subst k; omega
  have ho : owner (M z r) = some z := rfl
  cases v <;> simp [op, hk, afterD, afterC, hy, afterS, afterG,
    afterA, ho, hkz, afterJ]

theorem sameColumn {y z : T} (hy : owner y = none)
    (hdiag : y ≠ E z z) : op (op z y) y = R y (op z y) := by
  by_cases hzy : z = y
  · subst z
    cases hc : cert y with
    | some o =>
        rw [op_self_cert hc]
        exact op_cert_column hy hc
    | none =>
        rw [op_self_none y hy hc]
        exact op_R_column hy
  · cases y with
    | M k p => simp [owner] at hy
    | e =>
        by_cases hg : z = E e e
        · subst z
          simp [op, afterD, afterC, owner, afterS, afterG, afterA, afterJ]
        · rw [show op z e = R e z by
              simp [op, afterD, hzy, afterC, hy, afterS, afterG, hg,
                afterA_e]]
          simp [op, afterD, afterC, owner, afterS, afterG, afterA_e]
    | R k p =>
        by_cases hzk : z = k
        · subst z
          have hmk : M k p ≠ k := by
            intro h; have hs := congrArg sz h; simp [sz] at hs; omega
          rw [show op k (R k p) = M k p by
                simp [op, afterD, hzy, afterC, hy, afterS]]
          simp [op, afterD, afterC, owner, afterS, hmk, afterG, afterA_R]
        · by_cases hg : z = E (R k p) (R k p)
          · subst z
            have hmk : M (E (R k p) (R k p)) (R k p) ≠ k := by
              intro h; have hs := congrArg sz h; simp [sz] at hs; omega
            rw [show op (E (R k p) (R k p)) (R k p) =
                M (E (R k p) (R k p)) (R k p) by
                  simp [op, afterD, hzy, afterC, hy, afterS, hzk,
                    afterG]]
            simp [op, afterD, afterC, owner, afterS, hmk, afterG, afterA_R]
          · rw [show op z (R k p) = R (R k p) z by
                simp [op, afterD, hzy, afterC, hy, afterS, hzk,
                  afterG, hg, afterA_R]]
            exact op_R_column hy
    | E k v =>
        by_cases hzk : z = k
        · subst z
          have hvk : v ≠ k := by
            intro h
            subst v
            exact hdiag rfl
          rw [show op k (E k v) = v by simp [op]]
          exact op_decode_column hy hvk
        · by_cases hg : z = E (E k v) (E k v)
          · subst z
            have hlt : sz k < sz (E (E k v) (E k v)) := by
              simp [sz]
              omega
            rw [show op (E (E k v) (E k v)) (E k v) =
                M (E (E k v) (E k v)) (E k v) by
                  simp [op, hzk, afterD, hzy, afterC, hy, afterS,
                    afterG]]
            exact op_M_E_column_of_lt hy hlt
          · cases hz : owner z with
            | none =>
                rw [show op z (E k v) = R (E k v) z by
                  simp [op, hzk, afterD, hzy, afterC, hy, afterS,
                    afterG, hg, afterA, hz]]
                exact op_R_column hy
            | some o =>
                have hfirst : op z (E k v) = afterA z (E k v) := by
                  simp [op, hzk, afterD, hzy, afterC, hy, afterS,
                    afterG, hg]
                rcases afterA_E_result hz with hR | ⟨r, hM, hlt⟩
                · rw [hfirst, hR]
                  exact op_R_column hy
                · rw [hfirst, hM]
                  exact op_M_E_column_of_lt hy hlt

theorem pOwner (y z : T) :
    owner (op y (op (op z y) y)) = some y := by
  cases hy : owner y with
  | none =>
      by_cases hdiag : y = E z z
      · subst y
        have hz : op z (E z z) = z := by simp [op]
        simpa only [hz] using diag_activation z
      · rw [sameColumn hy hdiag]
        have hop (x : T) : op y (R y x) = M y x := by
          have hne : y ≠ R y x := by
            intro h
            have hs := congrArg sz h
            simp [sz] at hs
            omega
          simp [op, afterD, hne, afterC, owner, afterS]
        rw [hop]
        simp [owner]
  | some q =>
      cases y with
      | e => simp [owner] at hy
      | R a p => simp [owner] at hy
      | M o p =>
          simp [owner] at hy
          subst q
          exact pOwner_marker o p z
      | E q' d =>
          cases d with
          | e => simp [owner] at hy
          | M a p => simp [owner] at hy
          | R a p => simp [owner] at hy
          | E s t =>
              by_cases hst : s = t
              · subst t
                cases hs : owner s with
                | none => simp [owner, hs] at hy
                | some o =>
                    by_cases hoq : o = q'
                    · subst q'
                      simp [owner, hs] at hy
                      subst q
                      exact pOwner_child hs z
                    · simp [owner, hs, hoq] at hy
              · simp [owner, hst] at hy

theorem source : EquationLHS T := by
  intro x y z
  symm
  exact sectionInv (pOwner y z) x

theorem target : ¬ EquationRHS T := by
  intro h
  have bad := h e e e e
  change e = E e e at bad
  simp at bad

end T

def certificate : Goal := ⟨T, inferInstance, T.source, T.target⟩

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5837_to_698 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_5837_to_698
