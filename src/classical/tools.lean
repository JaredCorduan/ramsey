open classical

namespace classical.tools

variables p q : Prop
variables (α : Type) (r s : α → Prop)
variables a : α

lemma neg_imp_as_conj : ¬(p → q) → p ∧ ¬q :=
begin
  intro h,
  cases (em q) with hq hnq,
  {
    have hpq : p → q, intros hhh, exact hq,
    apply absurd hpq h,
  },
  cases (em p) with hp hnp,
  { apply and.intro hp hnq },
  {
    have hpq : p → q,
      { intro hp, apply absurd hp hnp },
    apply absurd hpq h
  }
end

lemma conj_as_neg_imp : p ∧ ¬q → ¬(p → q):=
  by {intros h c, apply absurd (c h.left) h.right }

lemma rev_imp : (p → q) → ¬ q → ¬ p :=
  by {intros hpq hnq hp, apply absurd (hpq hp) hnq}

lemma dne (h : ¬ ¬ p) : p :=
  by_contradiction (assume h1: ¬ p, show false, from h h1)

lemma neg_universal_as_ex : ¬ (∀ x, ¬ r x) → ∃ x, r x :=
begin
  intro h,
  have hh : ¬ (∃ (x : α), r x) → (∀ (x : α), ¬ r x),
    apply forall_not_of_not_exists,
  have hhh : ¬ ¬ (∃ (x : α), r x),
    apply rev_imp (¬ ∃ (x : α), r x) (∀ (x : α), ¬r x) hh h,
  apply by_contradiction, intro c, apply hhh, exact c,
end

lemma dne_under_univ : (∀ z, ¬ ¬ r z) → (∀ z, r z) :=
  by { intros h z, have hh : ¬ ¬ r z, apply h z, apply dne, exact hh }

lemma contra_pos : (¬q → ¬p) → (p → q) :=
begin
  intros cp hp,
  have c : ¬ ¬ q, assume hnq: ¬ q, apply absurd hp (cp hnq),
  apply dne, exact c,
end

lemma demorgan_or : ¬ (p ∨ q) → ¬ p ∧ ¬ q :=
  assume h : ¬ (p ∨ q),
    ⟨λ hp : p, h (or.inl hp), λ hq : q, h (or.inr hq)⟩

end classical.tools
