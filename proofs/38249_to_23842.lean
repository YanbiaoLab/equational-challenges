-- Equation38249 → Equation23842
-- Recorded verdict: false
-- Premise: x = ((y ◇ ((x ◇ x) ◇ z)) ◇ y) ◇ y
-- Conclusion: x = ((y ◇ z) ◇ z) ◇ (w ◇ (u ◇ x))
-- Original submission SHA-256: 8c4a11a3eb99ad80f57d3d7bcf9cc48957eda5b345439ad22c4f28e8356147d6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ ((x ◇ x) ◇ z)) ◇ y) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((y ◇ z) ◇ z) ◇ (w ◇ (u ◇ x))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   

set_option maxRecDepth 10000

namespace submission

inductive T where
  | g : Nat → T
  | p : T → T → T
deriving DecidableEq

namespace T

def sz : T → Nat
  | g _ => 0
  | p a b => sz a + sz b + 1

def bterm (output tail : T) : T :=
  p (p output output) tail

def fterm (owner output tail : T) : T :=
  p (p owner (bterm output tail)) owner

inductive Code : T → T → T → Prop
  | base (owner output tail : T) :
      Code (fterm owner output tail) owner output
  | hit {owner output tail hitValue : T}
      (h : Code owner (bterm output tail) hitValue) :
      Code (p hitValue owner) owner output

theorem code_right_owned {first second output : T}
    (h : Code first second output) :
    ∃ left, first = p left second := by
  cases h with
  | base owner output tail =>
      exact ⟨p _ (bterm output tail), rfl⟩
  | @hit owner output tail hitValue h =>
      exact ⟨hitValue, rfl⟩

theorem code_cases {first second output : T}
    (h : Code first second output) :
    (∃ tail, first = fterm second output tail) ∨
    (∃ tail hitValue,
      first = p hitValue second ∧
      Code second (bterm output tail) hitValue) := by
  cases h with
  | base owner output tail =>
      exact Or.inl ⟨tail, rfl⟩
  | @hit owner output tail hitValue h =>
      exact Or.inr ⟨tail, hitValue, rfl, h⟩

theorem code_output_small {first second output : T}
    (h : Code first second output) :
    sz output < sz first := by
  cases h with
  | base owner output tail =>
      simp [fterm, bterm, sz] <;> omega
  | @hit owner output tail hitValue h =>
      rcases code_right_owned h with ⟨left, hshape⟩
      have hsize := congrArg sz hshape
      simp [bterm, sz] at hsize ⊢
      omega

theorem code_output_unique {first second output₁ output₂ : T}
    (h₁ : Code first second output₁)
    (h₂ : Code first second output₂) :
    output₁ = output₂ := by
  rcases code_cases h₁ with
      ⟨tail₁, hbase₁⟩ |
      ⟨tail₁, hitValue₁, hhit₁, hrec₁⟩
  · rcases code_cases h₂ with
        ⟨tail₂, hbase₂⟩ |
        ⟨tail₂, hitValue₂, hhit₂, hrec₂⟩
    · have houter :
          fterm second output₁ tail₁ =
            fterm second output₂ tail₂ :=
        hbase₁.symm.trans hbase₂
      have hmiddle :
          bterm output₁ tail₁ =
            bterm output₂ tail₂ :=
        (p.inj (p.inj houter).1).2
      have hsquare :
          p output₁ output₁ =
            p output₂ output₂ :=
        (p.inj hmiddle).1
      exact (p.inj hsquare).1
    · have hhitValue :
          p second (bterm output₁ tail₁) =
            hitValue₂ :=
        (p.inj (hbase₁.symm.trans hhit₂)).1
      have hsmall := code_output_small hrec₂
      rw [← hhitValue] at hsmall
      simp [sz] at hsmall <;> omega
  · rcases code_cases h₂ with
        ⟨tail₂, hbase₂⟩ |
        ⟨tail₂, hitValue₂, hhit₂, hrec₂⟩
    · have hhitValue :
          hitValue₁ =
            p second (bterm output₂ tail₂) :=
        (p.inj (hhit₁.symm.trans hbase₂)).1
      have hsmall := code_output_small hrec₁
      rw [hhitValue] at hsmall
      simp [sz] at hsmall <;> omega
    · have hhitValue : hitValue₁ = hitValue₂ :=
        (p.inj (hhit₁.symm.trans hhit₂)).1
      subst hitValue₂
      rcases code_right_owned hrec₁ with
        ⟨left₁, hright₁⟩
      rcases code_right_owned hrec₂ with
        ⟨left₂, hright₂⟩
      have hencoded :
          bterm output₁ tail₁ =
            bterm output₂ tail₂ :=
        (p.inj (hright₁.symm.trans hright₂)).2
      have hsquare :
          p output₁ output₁ =
            p output₂ output₂ :=
        (p.inj hencoded).1
      exact (p.inj hsquare).1

noncomputable def eval (first second : T) : T := by
  classical
  exact if h : ∃ output, Code first second output
    then Classical.choose h
    else p first second

theorem eval_hit {first second output : T}
    (h : Code first second output) :
    eval first second = output := by
  rw [eval, dif_pos ⟨output, h⟩]
  exact code_output_unique
    (Classical.choose_spec ⟨output, h⟩) h

theorem eval_raw {first second : T}
    (h : ¬ ∃ output, Code first second output) :
    eval first second = p first second := by
  simp [eval, h]

theorem no_code_same (x : T) :
    ¬ ∃ output, Code x x output := by
  rintro ⟨output, h⟩
  rcases code_right_owned h with ⟨left, hshape⟩
  have hsize := congrArg sz hshape
  simp [sz] at hsize <;> omega

theorem no_code_pair_same (x : T) :
    ¬ ∃ output, Code (p x x) x output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨tail, hbase⟩ |
      ⟨tail, hitValue, hhit, hrec⟩
  · have hcycle :
        x = p x (bterm output tail) :=
      (p.inj hbase).1
    have hsize := congrArg sz hcycle
    simp [bterm, sz] at hsize <;> omega
  · have hhitValue : x = hitValue :=
      (p.inj hhit).1
    subst hitValue
    have hsmall := code_output_small hrec
    omega

theorem no_code_xx_z (x z : T) :
    ¬ ∃ output, Code (p x x) z output := by
  rintro ⟨output, h⟩
  rcases code_right_owned h with ⟨left, hshape⟩
  have hz : x = z := (p.inj hshape).2
  subst z
  exact no_code_pair_same x ⟨output, h⟩

theorem no_code_raw_middle (owner encoded : T) :
    ¬ ∃ output, Code (p owner encoded) owner output := by
  rintro ⟨output, h⟩
  rcases code_right_owned h with ⟨left, hshape⟩
  have hencoded : encoded = owner :=
    (p.inj hshape).2
  subst encoded
  exact no_code_pair_same owner ⟨output, h⟩

theorem no_code_after_hit
    {owner encoded hitValue : T}
    (h : Code owner encoded hitValue) :
    ¬ ∃ output, Code hitValue owner output := by
  rintro ⟨output, k⟩
  have hsmall := code_output_small h
  rcases code_right_owned k with ⟨left, hshape⟩
  have hsize := congrArg sz hshape
  simp [sz] at hsize
  omega

theorem source_eval (x y z : T) :
    eval
      (eval
        (eval y
          (eval (eval x x) z))
        y)
      y = x := by
  rw [eval_raw (no_code_same x)]
  rw [eval_raw (no_code_xx_z x z)]
  change
    eval
      (eval
        (eval y (bterm x z))
        y)
      y = x
  by_cases hcollision :
      ∃ hitValue, Code y (bterm x z) hitValue
  · let hitValue := Classical.choose hcollision
    have hhit : Code y (bterm x z) hitValue :=
      Classical.choose_spec hcollision
    rw [eval_hit hhit]
    rw [eval_raw (no_code_after_hit hhit)]
    exact eval_hit (Code.hit hhit)
  · rw [eval_raw hcollision]
    rw [eval_raw (no_code_raw_middle y (bterm x z))]
    exact eval_hit (Code.base y x z)

noncomputable instance instMagma : Magma T where
  op := eval

theorem source_holds (x y z : T) :
    x = ((y ◇ ((x ◇ x) ◇ z)) ◇ y) ◇ y := by
  change
    x =
      eval
        (eval
          (eval y
            (eval (eval x x) z))
          y)
        y
  exact (source_eval x y z).symm

def g0 : T := g 0
def t1 : T := p g0 g0
def t2 : T := p g0 t1
def t3 : T := p t2 g0
def t4 : T := p t3 g0
def t5 : T := p t4 g0

theorem no_code_first_atom (second : T) :
    ¬ ∃ output, Code g0 second output := by
  rintro ⟨output, h⟩
  rcases code_right_owned h with ⟨left, hshape⟩
  cases hshape

theorem no_code_t2_g :
    ¬ ∃ output, Code t2 g0 output := by
  rintro ⟨output, h⟩
  rcases code_right_owned h with ⟨left, hshape⟩
  have hbad : t1 = g0 :=
    (p.inj hshape).2
  cases hbad

theorem no_code_t3_g :
    ¬ ∃ output, Code t3 g0 output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨tail, hbase⟩ |
      ⟨tail, hitValue, hhit, hrec⟩
  · have hleft :
        t2 = p g0 (bterm output tail) :=
      (p.inj hbase).1
    have hencoded :
        t1 = bterm output tail :=
      (p.inj hleft).2
    have hbad :
        g0 = p output output :=
      (p.inj hencoded).1
    cases hbad
  · exact no_code_first_atom (bterm output tail)
      ⟨hitValue, hrec⟩

theorem no_code_t4_g :
    ¬ ∃ output, Code t4 g0 output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨tail, hbase⟩ |
      ⟨tail, hitValue, hhit, hrec⟩
  · have hleft :
        t3 = p g0 (bterm output tail) :=
      (p.inj hbase).1
    have hbad : t2 = g0 :=
      (p.inj hleft).1
    cases hbad
  · exact no_code_first_atom (bterm output tail)
      ⟨hitValue, hrec⟩

theorem target_rhs_value :
    (((g0 ◇ (g0 ◇ g0)) ◇ g0) ◇ g0) ◇ g0 = t5 := by
  change
    eval
      (eval
        (eval
          (eval g0 (eval g0 g0))
          g0)
        g0)
      g0 = t5
  have h1 : eval g0 g0 = t1 := by
    exact eval_raw (no_code_first_atom g0)
  rw [h1]
  have h2 : eval g0 t1 = t2 := by
    exact eval_raw (no_code_first_atom t1)
  rw [h2]
  have h3 : eval t2 g0 = t3 := by
    exact eval_raw no_code_t2_g
  rw [h3]
  have h4 : eval t3 g0 = t4 := by
    exact eval_raw no_code_t3_g
  rw [h4]
  exact eval_raw no_code_t4_g

theorem bad40590 :
    g0 ≠ (((g0 ◇ (g0 ◇ g0)) ◇ g0) ◇ g0) ◇ g0 := by
  rw [target_rhs_value]
  intro h
  cases h

end T

end submission

open submission

namespace submission
namespace T

def IsGenerator : T → Prop
  | .g _ => True
  | .p _ _ => False

def a1 : T := p t1 g0
def a2 : T := p a1 g0

theorem gg_value : eval g0 g0 = t1 := by
  exact eval_raw (no_code_first_atom g0)

theorem no_code_t1_g : ¬ ∃ output, Code t1 g0 output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨tail, hbase⟩ |
      ⟨tail, hitValue, hhit, hrec⟩
  · simp [t1, g0, fterm, bterm] at hbase
  · exact no_code_first_atom (bterm output tail) ⟨hitValue, hrec⟩

theorem no_code_a1_g : ¬ ∃ output, Code a1 g0 output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨tail, hbase⟩ |
      ⟨tail, hitValue, hhit, hrec⟩
  · simp [a1, t1, g0, fterm, bterm] at hbase
  · exact no_code_first_atom (bterm output tail) ⟨hitValue, hrec⟩

theorem no_code_a1_t2 : ¬ ∃ output, Code a1 t2 output := by
  rintro ⟨output, h⟩
  rcases code_right_owned h with ⟨left, hshape⟩
  simp [a1, t2, t1, g0] at hshape

theorem t1g_value : eval t1 g0 = a1 := by
  exact eval_raw no_code_t1_g

theorem a1g_value : eval a1 g0 = a2 := by
  exact eval_raw no_code_a1_g

theorem gt1_value : eval g0 t1 = t2 := by
  exact eval_raw (no_code_first_atom t1)

theorem a1t2_value : eval a1 t2 = p a1 t2 := by
  exact eval_raw no_code_a1_t2

end T
end submission

open submission

noncomputable def submission : Goal := by
  refine ⟨T, T.instMagma, ?_, ?_⟩
  · intro x y z
    exact T.source_holds x y z
  · intro target
    have bad := target T.g0 T.g0 T.g0 T.g0 T.g0
    change
      T.g0 =
        T.eval (T.eval (T.eval T.g0 T.g0) T.g0)
          (T.eval T.g0 (T.eval T.g0 T.g0)) at bad
    rw [T.gg_value, T.t1g_value, T.gt1_value, T.a1t2_value] at bad
    exact Eq.mp (congrArg T.IsGenerator bad) True.intro

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_38249_to_23842 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_38249_to_23842
