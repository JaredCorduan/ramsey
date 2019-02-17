import constructive.pigeon
import classical.tools

namespace classical.pigeon

open constructive.pigeon
open set

def cofinite (A : set ℕ) := ∃ x : ℕ, ∀ y : ℕ, y ≥ x → A y
def infinite (A : set ℕ) := ∀ x : ℕ, ∃ y : ℕ, y ≥ x ∧ A y

lemma x_le_fx_incr (f : ℕ → ℕ) (x : ℕ): increasing f → x ≤ f (x) :=
λ (incr : increasing f),
  nat.rec_on x (nat.zero_le (f 0))
    (λ (n : ℕ) (ih : n ≤ f n),
      nat.le_trans (nat.succ_le_succ ih) (incr n (nat.succ n) (nat.lt_succ_self n)))

lemma cofinite_implies_almost_full (A : set ℕ) : cofinite A → almost_full A :=
λ (h : cofinite A),
  exists.elim h
    (λ (x : ℕ) (HAx : (λ (x : ℕ), ∀ (y : ℕ), y ≥ x → A y) x),
       exists.intro (λ (f : ℕ → ℕ), f x)
         (λ (f : ℕ → ℕ) (incrf : increasing f),
            HAx (f ((λ (f : ℕ → ℕ), f x) f))
              (nat.le_trans (x_le_fx_incr f x incrf) (x_le_fx_incr f (f x) incrf))))

def failure_past (A : set ℕ) (x y : ℕ) := y ≥ x ∧ ¬ A y

def iter (f : ℕ → ℕ) : ℕ → ℕ
  | 0 := f 1
  | (n+1) := f ((iter n)+1)

lemma iter_incr (A : set ℕ) (f : ℕ → ℕ) :
  (∀ x : ℕ, f x ≥ x) → increasing (iter f) :=
  λ (h : ∀ (x : ℕ), f x ≥ x),
    increasing_by_step (iter f) (λ (n : ℕ), h (nat.succ (iter f n)))

open classical
open classical.tools

lemma not_cofinite (A : set ℕ) :
  ¬ cofinite A → (∀ x : ℕ, ∃ y : ℕ, failure_past A x y) :=
  λ (cofA : ¬cofinite A) (x : ℕ),
    exists.elim
      (neg_universal_as_ex ℕ (λ (z : ℕ), ¬(z ≥ x → A z))
        (λ (c : ∀ (m : ℕ), ¬¬(m ≥ x → A m)),
           absurd (dne_under_univ ℕ (λ (w : ℕ), w ≥ x → A w) c) (forall_not_of_not_exists cofA x)))
      (λ (w : ℕ) (eh : ¬(w ≥ x → A w)), exists.intro w (neg_imp_as_conj (w ≥ x) (A w) eh))

lemma increasing_failures (A : set ℕ) (f : ℕ → ℕ) :
  (∀ x : ℕ, failure_past A x (f x)) → increasing (iter f):=
  λ (h : ∀ (x : ℕ), failure_past A x (f x)), iter_incr A f (λ (x : ℕ), (h x).left)

lemma wit_not_A (A : set ℕ) (f : ℕ → ℕ) :
  (∀ x : ℕ, failure_past A x (f x)) → ∀ x : ℕ, ¬ A ((iter f) x) :=
  λ (h : ∀ (x : ℕ), pigeon.failure_past A x (f x)) (x : ℕ),
    nat.cases_on x ((h 1).right) (λ (x : ℕ), (h (pigeon.iter f x + 1)).right)

lemma not_cof_has_incr_wit (A : set ℕ) : ¬ cofinite A →
  ∃ f : ℕ → ℕ, (increasing (iter f)) ∧ (∀ x : ℕ, ¬ A ((iter f) x)) :=
  λ (nCofA : ¬pigeon.cofinite A),
    exists.elim (axiom_of_choice (not_cofinite A nCofA))
      (λ (f : Π (x : ℕ), (λ (x : ℕ), ℕ) x)
       (hf : ∀ (x : ℕ), (λ (x y : ℕ), pigeon.failure_past A x y) x (f x)),
         exists.intro f ⟨increasing_failures A f hf, wit_not_A A f hf⟩)

lemma almost_full_implies_cofinite (A : set ℕ) : ¬ cofinite A → ¬ almost_full A :=
λ (nCofA : ¬pigeon.cofinite A),
  exists.elim (not_cof_has_incr_wit A nCofA)
    (λ (f : ℕ → ℕ) (hf : increasing (pigeon.iter f) ∧ ∀ (x : ℕ), ¬A (pigeon.iter f x)),
       (λ (c : almost_full A),
          Exists.dcases_on c
            (λ (Y : (ℕ → ℕ) → ℕ) (hY : full A Y),
               absurd (hY (pigeon.iter f) (hf.left)) (hf.right (Y (pigeon.iter f))))))

theorem cofinite_is_almost_full (A : set ℕ) : cofinite A ↔ almost_full A :=
  {
     mp := pigeon.cofinite_implies_almost_full A,
     mpr := contra_pos (almost_full A) (pigeon.cofinite A) (almost_full_implies_cofinite A)
  }

def comp (A : set ℕ) := λ n : ℕ, ¬ A n

lemma not_infinite_has_wit (A : set ℕ) :
  ¬ infinite A → ∃ x : ℕ, ¬ (∃ y : ℕ, y ≥ x ∧ A y) :=
  λ (h : ¬pigeon.infinite A),
    neg_universal_as_ex ℕ (λ (x : ℕ), ¬∃ (y : ℕ), y ≥ x ∧ A y)
      (λ (c : ∀ (x : ℕ), ¬¬∃ (y : ℕ), y ≥ x ∧ A y),
         absurd (dne_under_univ ℕ (λ (x : ℕ), ∃ (y : ℕ), y ≥ x ∧ A y) c) h)

lemma not_infinite_co_cofinite (A : set ℕ) :
  ¬ infinite A → cofinite (comp A) :=
λ (h : ¬pigeon.infinite A),
  exists.elim (not_infinite_has_wit A h)
    (λ (w : ℕ) (wMax : ¬∃ (y : ℕ), y ≥ w ∧ A y),
       exists.intro w
         (λ (y : ℕ) (hyw : y ≥ w),
           (λ (c : A y),
             absurd
               (and.intro hyw c)
               (( @forall_not_of_not_exists ℕ (λ n : ℕ, n ≥ w ∧ A n) wMax) y))))

theorem pigeon (A : set ℕ) : infinite A ∨ infinite (comp A) :=
  by_contradiction
    (λ (c : ¬(pigeon.infinite A ∨ pigeon.infinite (comp A))),
       exists.elim
         (constr_pigeon (comp A) (comp (comp A))
            (pigeon.cofinite_implies_almost_full (comp A)
               (not_infinite_co_cofinite A
                 ((demorgan_or (pigeon.infinite A) (pigeon.infinite (comp A)) c).left)))
            (pigeon.cofinite_implies_almost_full (comp (comp A))
               (not_infinite_co_cofinite (comp A)
                  ((demorgan_or (pigeon.infinite A) (pigeon.infinite (comp A)) c).right))))
         (λ (Y : (ℕ → ℕ) → ℕ) (hY : full (comp A ∩ comp (comp A)) Y),
            absurd
              ((hY id (λ (x y : ℕ) (h : x < y), h)).left)
              ((hY id (λ (x y : ℕ) (h : x < y), h)).right)))

end classical.pigeon
