open classical

namespace classical.tools

variables p q : Prop
variables (α : Type) (r s : α → Prop)
variables a : α

lemma neg_imp_as_conj : ¬(p → q) → p ∧ ¬q :=
λ (h : ¬(p → q)),
  or.cases_on (em q)
    (λ (hq : q), absurd (λ (hhh : p), hq) h)
    (λ (hnq : ¬q),
       or.cases_on (em p)
         (λ (hp : p), ⟨hp, hnq⟩)
         (λ (hnp : ¬p), absurd (λ (hp : p), absurd hp hnp) h))

lemma conj_as_neg_imp : p ∧ ¬q → ¬(p → q):=
  λ (h : p ∧ ¬q), id (λ (c : p → q), absurd (c (h.left)) (h.right))

lemma rev_imp : (p → q) → ¬ q → ¬ p :=
  λ (hpq : p → q) (hnq : ¬q), id (λ (hp : p), absurd (hpq hp) hnq)

lemma dne (h : ¬ ¬ p) : p :=
  by_contradiction (assume h1: ¬ p, show false, from h h1)

lemma neg_universal_as_ex : ¬ (∀ x, ¬ r x) → ∃ x, r x :=
  λ (h : ¬∀ (x : α), ¬r x),
    by_contradiction
      (λ (c : ¬∃ (x : α), r x),
        rev_imp (¬∃ (x : α), r x) (∀ (x : α), ¬r x) forall_not_of_not_exists h c)

lemma dne_under_univ : (∀ z, ¬ ¬ r z) → (∀ z, r z) :=
  λ (h : ∀ (z : α), ¬¬r z) (z : α), dne (r z) (h z)

lemma contra_pos : (¬q → ¬p) → (p → q) :=
  λ (cp : ¬q → ¬p) (hp : p), dne q (id (λ (hnq : ¬q), absurd hp (cp hnq)))

lemma demorgan_or : ¬ (p ∨ q) → ¬ p ∧ ¬ q :=
  assume h : ¬ (p ∨ q),
    ⟨λ hp : p, h (or.inl hp), λ hq : q, h (or.inr hq)⟩

end classical.tools
