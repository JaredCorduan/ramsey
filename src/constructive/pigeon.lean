/-
Implemetation of:

Wim Veldman and Marc Bezem, Ramsey's Theorem and the Pigeon Hole
Principle in intuitionistic mathematics, Journal of the London
Mathematical Society (2), Vol. 47, April 1993, pp. 193-211.

Adapted from https://github.com/coq-contribs/ramsey/blob/master/Ramsey.v
-/

namespace constructive.pigeon

def increasing (f : ℕ → ℕ) :=
  ∀ x y : ℕ, x < y → f x < f y

def full (A : ℕ → Prop) (Y : (ℕ → ℕ) → ℕ) :=
∀ f : ℕ → ℕ, increasing f → A (f (Y f))

def almost_full (A : ℕ → Prop) := ∃ Y : (ℕ → ℕ) → ℕ, full A Y

lemma compose_increasing (f g : ℕ → ℕ) :
  increasing f → increasing g → increasing (λ x, f (g x)) :=
    λ (hf : increasing f) (hg : increasing g) (x y : ℕ) (h : x < y),
      hf (g x) (g y) (hg x y h)

lemma increasing_by_step (f : ℕ → ℕ) : (∀ n : ℕ, f n < f (n+1)) → increasing f :=
begin
  intros hf x y,
  apply nat.rec_on y,
    {
      intro contr, apply absurd contr (nat.not_succ_le_zero x) },
    intros z ih h,
    have hxz : x = z ∨ x < z,
      { apply nat.eq_or_lt_of_le (nat.le_of_lt_succ h) },
    cases hxz,
    rewrite hxz, exact (hf z),
    exact nat.lt_trans (ih hxz) (hf z),
end

def enumerate (Y : (ℕ → ℕ) → ℕ) : ℕ → ℕ
  | 0 := Y (id)
  | (n+1) := Y (λ m, m + (enumerate n) + 1) + (enumerate n) + 1

lemma  increasing_enumerate (Y : (ℕ → ℕ) → ℕ) : increasing (enumerate Y) :=
begin
  intro x, apply increasing_by_step,
  intro n,
  unfold enumerate, simp,
  apply nat.lt_add_of_pos_right,
  rewrite nat.add_comm, apply nat.zero_lt_succ
end

variables A B : ℕ → Prop
variables YA YB : (ℕ → ℕ)  → ℕ

def FYA (x n : ℕ) := n + nat.succ (enumerate YA x)

lemma increasing_FYA : ∀ x : ℕ, increasing (FYA YA x) :=
begin
  intros x y z h,
  apply nat.add_lt_add_right, exact h
end

lemma enumerate_YA : full A YA → ∀ x : ℕ, A (enumerate YA x) :=
begin
  intros fYA x,
  cases x with,
  { apply (fYA id), intros x y h, exact h },
  { apply fYA (FYA YA x), apply increasing_FYA }
end

lemma YB_enumerate_YA : full B YB -> B (enumerate YA (YB (enumerate YA))) :=
begin
  intro YBfull,
  apply YBfull (enumerate YA) (increasing_enumerate YA)
end

lemma pre_pidgeon : full A YA → full B YB →
  A (enumerate YA (YB (enumerate YA))) ∧ B (enumerate YA (YB (enumerate YA))) :=
begin
  intros YAfull YBfull,
  split,
    { apply enumerate_YA, exact YAfull },
    { apply YB_enumerate_YA, exact YBfull }
end

def inter (A B : ℕ -> Prop) (n : ℕ) := A n ∧ B n
infix `∩` := inter

def restrict (Y : (ℕ → ℕ) → ℕ) (f : ℕ → ℕ) := λ g : ℕ → ℕ, Y (f ∘ g)

def combine (YA YB : (ℕ → ℕ) -> ℕ) (f : ℕ → ℕ) :=
  enumerate (restrict YA f) ((restrict YB f) (enumerate (restrict YA f)))
infix `⊙` : 50 := combine

theorem constr_pidgeon_with_wits (A B : nat -> Prop)
  (YA YB : (nat -> nat) -> nat) :
    full A YA → full B YB → full (A ∩ B) (YA ⊙ YB) :=
begin
  intros YAfull YBfull f incrf,
  apply pre_pidgeon (A ∘ f) (B ∘ f) (restrict YA f) (restrict YB f);
  {
    intros g incrg,
    apply YAfull (f∘g) <|> apply YBfull (f∘g),
    apply compose_increasing f g incrf incrg
  }
end

theorem constr_pigeon (A B : nat -> Prop) :
  almost_full A → almost_full B → almost_full (A ∩ B) :=
begin
  intros afA afB,
  cases afA with YA hYA,
  cases afB with YB hYB,
  unfold almost_full,
  have h : full (A ∩ B) (YA ⊙ YB),
    apply constr_pidgeon_with_wits A B YA YB hYA hYB,
  apply exists.intro (YA⊙YB) h,
end

end constructive.pigeon
