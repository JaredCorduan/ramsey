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
λ (hf : ∀ n : ℕ, f n < f (n+1)) (x y : ℕ),
  nat.rec_on y
    (λ (contr : x < 0), absurd contr (nat.not_succ_le_zero x))
    (λ (z : ℕ) (ih : x < z → f x < f z) (h : x < nat.succ z),
      or.cases_on (nat.eq_or_lt_of_le (nat.le_of_lt_succ h))
        (λ hxz : x = z, hxz ▸ (hf x))
        (λ (hxz : x < z), nat.lt_trans (ih hxz) (hf z)))

def enumerate (Y : (ℕ → ℕ) → ℕ) : ℕ → ℕ
  | 0 := Y (id)
  | (n+1) := Y (λ m, m + (enumerate n) + 1) + (enumerate n) + 1

lemma  increasing_enumerate (Y : (ℕ → ℕ) → ℕ) : increasing (enumerate Y) :=
λ x : ℕ,
increasing_by_step (λ (x : ℕ), enumerate Y x)
 (λ (n : ℕ),
   nat.le_add_left
     ((enumerate Y n)+1)
     (Y (λ (m : ℕ), m + enumerate Y (nat.add n 0) + 1))) x

variables A B : ℕ → Prop
variables YA YB : (ℕ → ℕ)  → ℕ

def FYA (x n : ℕ) := n + nat.succ (enumerate YA x)

lemma increasing_FYA : ∀ x : ℕ, increasing (FYA YA x) :=
λ (x : ℕ) (y z : ℕ) (h : y < z),
  nat.add_lt_add_right h (nat.succ (enumerate YA x))

lemma enumerate_YA : full A YA → ∀ x : ℕ, A (enumerate YA x) :=
λ (fYA : full A YA) (x : ℕ),
  nat.cases_on x
    (fYA id (λ (x y : ℕ) (h : x < y), h))
    (λ (x : ℕ), fYA (FYA YA x) (increasing_FYA YA x))

lemma YB_enumerate_YA : full B YB -> B (enumerate YA (YB (enumerate YA))) :=
λ YBfull : full B YB,
  YBfull (enumerate YA) (increasing_enumerate YA)

lemma pre_pidgeon : full A YA → full B YB →
  A (enumerate YA (YB (enumerate YA))) ∧ B (enumerate YA (YB (enumerate YA))) :=
λ (YAfull : full A YA) (YBfull : full B YB),
  ⟨enumerate_YA A YA YAfull (YB (enumerate YA)), YB_enumerate_YA B YA YB YBfull⟩

def inter (A B : ℕ -> Prop) (n : ℕ) := A n ∧ B n
infix `∩` := inter

def restrict (Y : (ℕ → ℕ) → ℕ) (f : ℕ → ℕ) := λ g : ℕ → ℕ, Y (f ∘ g)

def combine (YA YB : (ℕ → ℕ) -> ℕ) (f : ℕ → ℕ) :=
  enumerate (restrict YA f) ((restrict YB f) (enumerate (restrict YA f)))
infix `⊙` : 50 := combine

theorem constr_pidgeon_with_wits (A B : nat -> Prop)
  (YA YB : (nat -> nat) -> nat) :
    full A YA → full B YB → full (A ∩ B) (YA ⊙ YB) :=
λ (YAfull : full A YA) (YBfull : full B YB),
    λ (f : ℕ → ℕ) (incrf : increasing f),
       pre_pidgeon (A ∘ f) (B ∘ f) (restrict YA f) (restrict YB f)
         (λ (g : ℕ → ℕ) (incrg : increasing g),
           YAfull (f ∘ g) (compose_increasing f g incrf incrg))
         (λ (g : ℕ → ℕ) (incrg : increasing g),
           YBfull (f ∘ g) (compose_increasing f g incrf incrg))

theorem constr_pigeon (A B : nat -> Prop) :
  almost_full A → almost_full B → almost_full (A ∩ B) :=
λ (afA : almost_full A) (afB : almost_full B),
  exists.elim afA
    (λ (YA : (ℕ → ℕ) → ℕ) (hYA : full A YA),
       exists.elim afB
         (λ (YB : (ℕ → ℕ) → ℕ) (hYB : full B YB),
              (exists.intro
                (YA⊙YB) (constr_pidgeon_with_wits A B YA YB hYA hYB))))

end constructive.pigeon
