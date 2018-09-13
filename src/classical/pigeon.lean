import constructive.pigeon
import classical.tools

namespace classical.pigeon

open constructive.pigeon

def cofinite (A : ℕ → Prop) := ∃ x : ℕ, ∀ y : ℕ, y ≥ x → A y
def infinite (A : ℕ → Prop) := ∀ x : ℕ, ∃ y : ℕ, y ≥ x ∧ A y

lemma x_le_fx_incr (f : ℕ → ℕ) (x : ℕ): increasing f → x ≤ f (x) :=
begin
  intros incr,
  apply nat.rec_on x,
  { apply nat.zero_le },
  { intros n ih,
    have h : f n < f (nat.succ n),
      apply incr n (nat.succ n) (nat.lt_succ_self n),
    apply nat.le_trans (nat.succ_le_succ ih) h }
end

lemma cofinite_implies_almost_full (A : ℕ → Prop) : cofinite A → almost_full A :=
begin
  intros h, apply (exists.elim h), intros x HAx,
  apply exists.intro (λ f : ℕ → ℕ, f (x)),
  intros f incrf,
  apply HAx,
  apply nat.le_trans
    (x_le_fx_incr f x incrf) (x_le_fx_incr f (f x) incrf),
end

def failure_past (A : ℕ → Prop) (x y : ℕ) := y ≥ x ∧ ¬ A y

def iter (f : ℕ → ℕ) : ℕ → ℕ
  | 0 := f 1
  | (n+1) := f ((iter n)+1)

lemma iter_incr (A : ℕ → Prop) (f : ℕ → ℕ) :
  (∀ x : ℕ, f x ≥ x) → increasing (iter f) :=
by {intro h, apply increasing_by_step, intro n, apply h}

open classical
open classical.tools

lemma not_cofinite (A : ℕ → Prop) :
  ¬ cofinite A → (∀ x : ℕ, ∃ y : ℕ, failure_past A x y) :=
begin
  intros cofA x,
  have h : ∃ y : ℕ, ¬ (y ≥ x → A y),
    apply neg_universal_as_ex, intro c,
    apply absurd
      (dne_under_univ ℕ (λ w : ℕ, w ≥ x → A w) c)
      ((forall_not_of_not_exists cofA) x),
  cases h with w eh,
  apply exists.intro w (neg_imp_as_conj (w ≥ x) (A w) eh),
end

lemma increasing_failures (A : ℕ → Prop) (f : ℕ → ℕ) :
  (∀ x : ℕ, failure_past A x (f x)) → increasing (iter f):=
begin
  intro h, apply iter_incr A,
  intro x, apply (h x).left,
end

lemma wit_not_A (A : ℕ → Prop) (f : ℕ → ℕ) :
  (∀ x : ℕ, failure_past A x (f x)) → ∀ x : ℕ, ¬ A ((iter f) x) :=
begin
  intros h x,
  cases x,
  apply (h 1).right,
  apply (h (iter f x + 1)).right
end

lemma almost_full_implies_cofinite (A : ℕ → Prop) :
  ¬ cofinite A → ¬ almost_full A :=
begin
  intro nCofA,
  have h : ∃ f : ℕ → ℕ, (increasing (iter f)) ∧ (∀ x : ℕ, ¬ A ((iter f) x)),
  {
    cases axiom_of_choice (not_cofinite A nCofA) with f hf,
    apply exists.intro f
    (and.intro (increasing_failures A f hf) (wit_not_A A f hf)),
  },
  cases h with f hf, intro c,
  cases c with Y hY,
  apply absurd (hY (iter f) hf.left) (hf.right (Y (iter f))),
end

theorem cofinite_is_almost_full (A : ℕ → Prop) : cofinite A ↔ almost_full A :=
  iff.intro
    (cofinite_implies_almost_full A)
    (contra_pos (almost_full A) (cofinite A) (almost_full_implies_cofinite A))

def comp (A : ℕ → Prop) := λ n : ℕ, ¬ A n

lemma not_infinite_co_cofinite (A : ℕ → Prop) :
  ¬ infinite A → cofinite (comp A) :=
begin
  intro h,
  have h₂ : ∃ x : ℕ, ¬ (∃ y : ℕ, y ≥ x ∧ A y),
  {
    apply neg_universal_as_ex,
    intro c,
    apply absurd
      (dne_under_univ ℕ (λ x : ℕ, ∃ y : ℕ, y ≥ x ∧ A y) c) h,
  },
  cases h₂ with w wMax,
  have h₃ : ∀ y : ℕ, ¬ (y ≥ w ∧ A y),
    { apply forall_not_of_not_exists, exact wMax },
  have h₄ :  ∀ (y : ℕ), y ≥ w → ¬ A y,
    { intros y hyw c,
      apply absurd (and.intro hyw c) (h₃ y) },
  apply exists.intro w h₄,
end

theorem pigeon (A : ℕ → Prop) :
  infinite A ∨ infinite (comp A) :=
by_contradiction
begin
  intro c,
  have h : ¬ (infinite A) ∧ ¬ (infinite (comp A)),
    apply demorgan_or, exact c,

  -- A and ¬A are cofinite
  have cfcA : cofinite (comp A),
    apply not_infinite_co_cofinite, exact h.left,
  have cfccA : cofinite (comp (comp A)),
    apply not_infinite_co_cofinite, exact h.right,

  -- A and ¬A are almost full
  have afcA : almost_full (comp A),
    apply cofinite_implies_almost_full (comp A) cfcA,
  have afccA : almost_full (comp (comp A)),
    apply cofinite_implies_almost_full (comp (comp A)) cfccA,

  -- So by the constructive pigeon hole principle,
  -- A ∩ ¬A = ∅ is almost full, which is absurd
  have contr : almost_full ((comp A) ∩ (comp (comp A))),
    apply constr_pigeon (comp A) (comp (comp A)) afcA afccA,
  cases contr with Y hY,
  have Yid : (comp A∩comp (comp A)) (id (Y id)),
    apply hY id, intros x y h, exact h,
  apply absurd Yid.left Yid.right,
end

end classical.pigeon
