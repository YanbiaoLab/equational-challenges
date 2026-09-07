-- Equation481 → Equation3161
-- Recorded verdict: false
-- Premise: x = y ◇ (x ◇ (y ◇ (z ◇ z)))
-- Conclusion: x = (((y ◇ y) ◇ z) ◇ x) ◇ z
-- Original submission SHA-256: e65a3597b280b8b5250174f71be483e859707260881e283e2f732a1f5173c05a
-- Aurora-accepted correction SHA-256: af2e743a1ef43865eec5025c48ef5e5493501e978dadd788aa5cea246ff8701e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (y ◇ (z ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((y ◇ y) ◇ z) ◇ x) ◇ z
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                     

set_option maxHeartbeats 0

namespace submission

inductive T where
  | leaf (n : Nat)
  | fork (x y : T)
  deriving DecidableEq

open T
def d := leaf 99

def q1 : T → Option T
  | (fork (y₁) (((fork (x) (((fork (y₂) (((fork (z₁) (z₂))))))))))) =>
      if y₁ = y₂ ∧ z₁ = z₂ then some x else none
  | _ => none

def q2 : T → Option T
  | (fork (((fork (z₁) (z₂)))) (((fork (x) (((fork (z₃) (z₄)))))))) =>
      if z₁ = z₂ ∧ z₁ = z₃ ∧ z₁ = z₄ then some x else none
  | _ => none

def r : T → T
  | t@((fork (p) (q))) => (q1 t).getD ((q2 t).getD (if p = q then (fork (d) (d)) else t))
  | t => t

def Normal : T → Prop
  | leaf _ => True
  | (fork (x) (y)) => Normal x ∧ Normal y ∧ r ((fork (x) (y))) = (fork (x) (y))

theorem dd_normal : Normal ((fork (d) (d))) := by simp [Normal, r, q1, q2, d]

theorem q1_closed {x y z : T} (hx : Normal x) (hy : Normal y)
    (h : q1 ((fork (x) (y))) = some z) : Normal z := by
  cases y with
  | leaf n => simp [q1] at h
  | fork u v =>
    cases v with
    | leaf n => simp [q1] at h
    | fork w t =>
      cases t with
      | leaf n => simp [q1] at h
      | fork a b =>
        simp only [q1] at h
        split at h
        · injection h with hz
          subst z
          exact hy.1
        · contradiction

theorem q2_closed {x y z : T} (hx : Normal x) (hy : Normal y)
    (h : q2 ((fork (x) (y))) = some z) : Normal z := by
  cases x with
  | leaf n => simp [q2] at h
  | fork a b =>
    cases y with
    | leaf n => simp [q2] at h
    | fork u v =>
      cases v with
      | leaf n => simp [q2] at h
      | fork c e =>
        simp only [q2] at h
        split at h
        · injection h with hz
          subst z
          exact hy.1
        · contradiction

theorem closed {x y : T} (hx : Normal x) (hy : Normal y) :
    Normal (r ((fork (x) (y)))) := by
  cases h1 : q1 ((fork (x) (y))) with
  | some z => simpa only [r, h1, Option.getD] using q1_closed hx hy h1
  | none =>
    cases h2 : q2 ((fork (x) (y))) with
    | some z => simpa only [r, h1, h2, Option.getD] using q2_closed hx hy h2
    | none =>
      by_cases he : x = y
      · subst x
        simpa only [r, h1, h2, if_pos, Option.getD] using dd_normal
      · have hr : r ((fork (x) (y))) = (fork (x) (y)) := by
          simp [r, h1, h2, he]
        rw [hr]
        exact ⟨hx, hy, hr⟩

def G := {t : T // Normal t}

instance : Magma G where
  op x y := ⟨r ((fork (x.1) (y.1))), closed x.2 y.2⟩

theorem fixed {x : T} (hx : Normal x) : r x = x := by
  cases x with
  | leaf n => rfl
  | fork x y => exact hx.2.2

def sz : T → Nat
  | leaf _ => 1
  | (fork (x) (y)) => sz x + sz y + 1

theorem q1_xx_none (x : T) : q1 ((fork (x) (x))) = none := by
  cases x with
  | leaf n => rfl
  | fork a t =>
    cases t with
    | leaf n => rfl
    | fork b u =>
      cases u with
      | leaf n => rfl
      | fork c e =>
        have hn : ¬(((fork (a) (((fork (b) (((fork (c) (e)))))))) : T) = b ∧ c = e) := by
          intro hc
          have hs := congrArg sz hc.1
          simp [sz] at hs
          omega
        simp [q1, hn]

theorem q2_xx_none (x : T) : q2 ((fork (x) (x))) = none := by
  cases x with
  | leaf n => rfl
  | fork a b =>
    cases b with
    | leaf n => rfl
    | fork c e =>
      have hn : ¬(a = (fork (c) (e)) ∧ a = c ∧ a = e) := by
        intro hc
        rcases hc with ⟨hself, hac, _⟩
        have hs1 := congrArg sz hself
        have hs2 := congrArg sz hac
        simp [sz] at hs1 hs2
        omega
      simp [q2, hn]

@[simp] theorem r_xx (x : T) : r ((fork (x) (x))) = (fork (d) (d)) := by
  simp [r, q1_xx_none, q2_xx_none]

theorem q2_special (x y : T) :
    q2 ((fork (x) (((fork (y) (((fork (d) (d))))))))) = if x = (fork (d) (d)) then some y else none := by
  cases x with
  | leaf n => simp [q2, d]
  | fork a b =>
    by_cases ha : a = d
    · subst a
      by_cases hb : b = d
      · subst b
        simp [q2, d]
      · have hb' : b ≠ leaf 99 := by simpa [d] using hb
        simp [q2, d, hb', eq_comm]
    · have ha' : a ≠ leaf 99 := by simpa [d] using ha
      simp [q2, d, ha', eq_comm]

theorem comp1_2 {x y : T} (hx : Normal x) :
    r ((fork (y) (r ((fork (x) (((fork (y) (((fork (d) (d)))))))))))) = x := by
  by_cases hxdd : x = (fork (d) (d))
  · subst x
    have hi : r ((fork (((fork (d) (d)))) (((fork (y) (((fork (d) (d))))))))) = y := by
      simp [r, q1, q2, d]
    rw [hi, r_xx]
  · by_cases hxy : x = (fork (y) (((fork (d) (d)))))
    · subst x
      have hy : y ≠ (fork (d) (d)) := by
        intro he
        subst y
        have hf := fixed hx
        simp [r, q1, q2, d] at hf
      have hi : r ((fork (((fork (y) (((fork (d) (d))))))) (((fork (y) (((fork (d) (d))))))))) = (fork (d) (d)) := r_xx _
      have hy' : y ≠ (fork (leaf 99) (leaf 99)) := by simpa [d] using hy
      have ho : r ((fork (y) (((fork (d) (d)))))) = (fork (y) (((fork (d) (d))))) := by
        simp [r, q1, q2, d, hy']
      rw [hi, ho]
    · have hi : r ((fork (x) (((fork (y) (((fork (d) (d))))))))) = (fork (x) (((fork (y) (((fork (d) (d)))))))) := by
        have hq1 : q1 ((fork (x) (((fork (y) (((fork (d) (d))))))))) = none := by simp [q1, d]
        simp only [r, hq1]
        rw [q2_special]
        simp [hxdd, hxy]
      rw [hi]
      simp [r, q1, q2, d]

theorem comp2_2 {x : T} (hx : Normal x) :
    r ((fork (((fork (d) (d)))) (r ((fork (x) (((fork (d) (d))))))))) = x := by
  by_cases hxdd : x = (fork (d) (d))
  · subst x
    simp [r, q1, q2, d]
  · have hi : r ((fork (x) (((fork (d) (d)))))) = (fork (x) (((fork (d) (d))))) := by
      have hq1 : q1 ((fork (x) (((fork (d) (d)))))) = none := by simp [q1, d]
      have hq2 : q2 ((fork (x) (((fork (d) (d)))))) = none := by simp [q2, d]
      simp [r, hq1, hq2, hxdd]
    rw [hi]
    simp [r, q1, q2, d]

theorem comp1_3 {x y : T} (hx : Normal x) :
    r ((fork (y) (r ((fork (x) (r ((fork (y) (((fork (d) (d)))))))))))) = x := by
  by_cases hydd : y = (fork (d) (d))
  · subst y
    rw [r_xx]
    exact comp2_2 hx
  · have hydd' : y ≠ (fork (leaf 99) (leaf 99)) := by simpa [d] using hydd
    have hi : r ((fork (y) (((fork (d) (d)))))) = (fork (y) (((fork (d) (d))))) := by
      simp [r, q1, q2, d, hydd']
    rw [hi]
    exact comp1_2 hx

theorem source : EquationLHS G := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
  apply Subtype.ext
  change x = r ((fork (y) (r ((fork (x) (r ((fork (y) (r ((fork (z) (z))))))))))))
  rw [r_xx]
  exact (comp1_3 hx).symm

def a : G := ⟨leaf 0, trivial⟩
def b : G := ⟨leaf 1, trivial⟩
def c : G := ⟨leaf 2, trivial⟩

theorem target_false : ¬ EquationRHS G := by
  intro h
  have q := congrArg Subtype.val (h a b c)
  simp [a, b, c, Magma.op, r, q1, q2, d] at q

end submission

def submission : Goal :=
  ⟨submission.G, submission.instMagmaG, submission.source, submission.target_false⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_481_to_3161 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_481_to_3161
