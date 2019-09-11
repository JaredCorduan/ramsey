import classical.pigeon
import logic.basic
import data.set.basic

open set
open classical
open nat

section ramsey_2_2

def infinite (H : set ℕ) := ∀ x : ℕ, ∃ y : ℕ, x < y ∧ y ∈ H

inductive color
| red : color
| blue : color

structure Inf :=
(s : set ℕ)
(pf : infinite s)

instance : has_coe Inf (set ℕ) := ⟨Inf.s⟩
instance : has_mem ℕ Inf := ⟨λ n H, n ∈ H.s⟩
instance : has_subset Inf := ⟨λ H₁ H₂, H₁.s ⊆ H₂.s⟩

open color

def reds (f : ℕ → color) (H : set ℕ) := (λ n : ℕ, f n = red ∧ n ∈ H )
def blues (f : ℕ → color) (H : set ℕ) := (λ n : ℕ, f n = blue ∧ H n)

lemma lt_succ_sum : forall x y : ℕ, x < x + y + 1 :=
λ x y : ℕ, lt_add_of_pos_right x (succ_pos y)

def sizeTwoSets (S : set ℕ) :=
  {p : ℕ × ℕ // p.fst < p.snd ∧ S p.fst ∧ S p.snd}
notation `[ℕ]²` := sizeTwoSets univ
notation `[` S `]²` := sizeTwoSets S

def project (f : [ℕ]² → color) (m : ℕ) : ℕ → color :=
  λ n : ℕ,
    dite (m < n)
      (λ h : m < n, f (subtype.mk (m, n) ⟨h, trivial, trivial⟩))
      (λ _, red)

lemma project_eq (f : [ℕ]² → color) (p : [ℕ]²):
  f p = project f p.val.fst p.val.snd :=
begin
  unfold project,
  simp [p.property.left]
end

def homogeneous (f : ℕ → color) (H : Inf) :=
  ∃ c : color, ∀ n, n ∈ H → f n = c

structure condition (f : [ℕ]² → color) extends Inf := (pt : ℕ)
instance (f : [ℕ]² → color) : has_coe (condition f) Inf := ⟨λ c, c.to_Inf⟩

def ext {f : [ℕ]² → color} (p q: condition f) :=
p.pt < q.pt ∧ q.pt ∈ p.s ∧ q.s ⊆ p.s ∧ homogeneous (project f q.pt) q

infix `<<`:50 := ext

local attribute [instance] prop_decidable

-- This is a version of the PHP tailored to our use case
lemma pigeon_hole_principle (f : ℕ → color) (H : Inf):
  infinite (reds f H) ∨ infinite (blues f H) :=
begin
  rw or_iff_not_imp_left,
  intros redFin,
  simp [infinite, not_forall, not_exists] at redFin,
  cases redFin with w Hw,
  intros x,
  have x_lt_a : x < x + w + 1, exact lt_succ_sum x w,
  have w_lt_a : w < x + w + 1,
    { simp, exact lt_succ_sum w x },
  let a : ℕ := x + w + 1,
    cases (H.pf a) with b Hb,
  have w_lt_b : w < b, exact nat.lt_trans w_lt_a Hb.left,
  have hrb : f b = red ∨ f b = blue,
    { cases f b, simp, simp },
  apply exists.intro b,
  constructor,
  { exact nat.lt_trans x_lt_a Hb.left },
  {
    cases hrb with hRed hBlue,
    { exact absurd (and.intro hRed Hb.right) (Hw b w_lt_b) },
    { exact ⟨hBlue, Hb.right⟩ }
  }
end

lemma extend_condition (f : [ℕ]² → color) :
  ∀ (p : condition f), ∃ q : condition f, p << q :=
begin
  intros p,
  cases p.pf p.pt with x Hx,
  have Hinf :
    infinite (reds (project f x) p.s) ∨ infinite (blues (project f x) p.s),
    apply pigeon_hole_principle,
  cases Hinf,
  any_goals { -- Red Case
    apply exists.intro (condition.mk f ⟨reds (project f x) p.s, Hinf⟩ x),
  },
  any_goals { -- Blue Case
    apply exists.intro (condition.mk f ⟨blues (project f x) p.s, Hinf⟩ x)
  },
  all_goals
  {
    constructor,
    { exact Hx.left },
    constructor,
    { exact Hx.right },
    constructor,
    { intros n Hn, exact Hn.right },
    { apply exists.intro, intros n Hn, exact Hn.left },
  }
end

-- This is just ℕ, but with type Inf
def NatInf : Inf := Inf.mk univ
begin
  intro x, apply exists.intro (x+1),
  constructor, exact lt_succ_sum x 0, trivial,
end

-- The initiall condition is just ℕ with 0.
def initCond (f : [ℕ]² → color) := (⟨f, NatInf, 0⟩ : condition f)

-- Condition choice function
def condition_cf (f : [ℕ]² → color) :=
  Π (x : condition f), (λ (x : condition f), condition f) x

-- Used to create the sequence of conditions
def extend_sequence (f : [ℕ]² → color) (cf : condition_cf f) :
  ℕ → condition f
| 0 := cf (initCond f)
| (n+1) := let p := extend_sequence n in cf ⟨f, p, p.pt⟩

lemma exists_condition_seq (f : [ℕ]² → color) :
∃ (g : ℕ → condition f), initCond f << g 0 ∧ ∀ n, g n << g (n+1) :=
begin
  have ac : ∃ (r : condition_cf f),
    ∀ (p : condition f), (λ (p q : condition f), p<<q) p (r p),
    exact axiom_of_choice (extend_condition f),
  cases ac with cf Hcf,
  let g := λ m : ℕ, (extend_sequence f cf m),
  apply exists.intro g,
  constructor,
  {
    exact Hcf (initCond f)
  },
  {
    intro n,
    have h1 : (extend_sequence f cf n) << cf (extend_sequence f cf n),
      exact Hcf (extend_sequence f cf n),
    have h2 : ∀ p : condition f, p = ⟨f, ↑p, p.pt⟩,
      intro p, cases p with H n, cases H with s pf, refl,
    have h3 : cf (extend_sequence f cf n) = extend_sequence f cf (n+1),
      unfold extend_sequence, simp, rw ← (h2 (extend_sequence f cf n)),
    simp * at *
  }
end

lemma cond_seq_mono_sets
  (f : [ℕ]² → color)
  (g : ℕ → condition f)
  (h : ∀ n, g n << g (n+1))
  (x y : ℕ) :
  (g (x+y)).s ⊆ (g x).s :=
begin
  induction y with y ih,
  {
    intros y hy, exact hy,
  },
  {
    intros a ha,
    exact ih ((h (x+y)).right.right.left ha),
  }
end

lemma cond_seq_mono_pts
  (f : [ℕ]² → color)
  (g : ℕ → condition f)
  (h : ∀ n, g n << g (n+1))
  (x y : ℕ) :
  (g (x+y+1)).pt ∈ (g x).s :=
by exact (cond_seq_mono_sets f g h x y) ((h (x+y)).right.left)

lemma cond_seq_stable_colors
  (f : [ℕ]² → color)
  (g : ℕ → condition f)
  (h0 : (initCond f) << g 0)
  (hn : ∀ n, g n << g (n+1))
  (x y : ℕ) :
  (project f (g x).pt) (g (x+1)).pt = (project f (g x).pt) (g (x+y+1)).pt :=
begin
  cases x,
  {
    have h : homogeneous (project f (g 0).pt) (g 0),
      exact h0.right.right.right,
    cases h with c hm,
    simp,
    rw hm ((g 1).pt) (cond_seq_mono_pts f g hn 0 0),
    have hzy : y + 1 = 0 + y + 1, simp,
    rw hzy,
    rw hm ((g (0+y+1)).pt) (cond_seq_mono_pts f g hn 0 y),
  },
  {
    have hgx : g x << g (x+1), exact (hn x),
    have hm : homogeneous (project f (g (x+1)).pt) (g (x+1)),
      exact hgx.right.right.right,
    cases hm with c Hm',
    rw Hm' ((g (x + 1 + 1)).pt) (cond_seq_mono_pts f g hn (x+1) 0),
    rw Hm' ((g (x + 1 + y + 1)).pt) (cond_seq_mono_pts f g hn (x+1) y),
  }
end

section increasing_functions

def increasing (f : ℕ → ℕ) := ∀ x y : ℕ, x < y → f x < f y

lemma increasing_by_step (f : ℕ → ℕ) :
  (∀ n : ℕ, f n < f (n+1)) → increasing f :=
λ (hf : ∀ n : ℕ, f n < f (n+1)) (x y : ℕ), nat.rec_on y
(λ (contr : x < 0), absurd contr (nat.not_succ_le_zero x))
(λ (z : ℕ) (ih : x < z → f x < f z) (h : x < nat.succ z),
or.cases_on (nat.eq_or_lt_of_le (nat.le_of_lt_succ h))
(λ hxz : x = z, hxz ▸ (hf x))
(λ (hxz : x < z), nat.lt_trans (ih hxz) (hf z)))

lemma x_le_fx_incr (f : ℕ → ℕ) (x : ℕ): increasing f → x ≤ f x :=
λ (incr : increasing f),
  nat.rec_on x (nat.zero_le (f 0))
  (λ (n : ℕ) (ih : n ≤ f n),
  nat.le_trans (nat.succ_le_succ ih) (incr n (nat.succ n) (nat.lt_succ_self n)))

lemma incr_range_inf (H : Inf) (g : ℕ → ℕ) (hg : increasing g) :
  infinite (image g H) :=
begin
  intros x,
  have h : ∃ h, x < h ∧ h ∈ H, exact H.pf x,
  cases h with h Hh,
  apply exists.intro (g h),
  constructor,
  exact (lt_of_lt_of_le Hh.left (x_le_fx_incr g h hg)),
  unfold image,
  apply exists.intro h, constructor, exact Hh.right, refl,
end

lemma incr_dom (g : ℕ → ℕ) (hg : increasing g) (x y : ℕ) (h : g x < g y):
  x < y :=
begin
  cases (lt_trichotomy x y) with hlt hlte,
    exact hlt,
    cases hlte with hlt he, rw hlt at h,
    exact absurd h (lt_irrefl (g y)),
    exact absurd (lt_trans (hg y x he) h) (lt_irrefl (g y)),
end

end increasing_functions

lemma domain_dist_rw (x y : ℕ) (h : x < y): y = x + (y - (x+1)) + 1 :=
by rw [ add_assoc x (y - (x+1)) 1
      , add_comm (y - (x+1)) 1
      , ←add_assoc x 1 (y - (x+1))
      , add_sub_of_le (succ_le_of_lt h)]

lemma cond_seq_incr
(f : [ℕ]² → color)
(g : ℕ → condition f)
(h : ∀ n, g n << g (n+1)) :
increasing (λ n : ℕ, (g n).pt) :=
begin
have h : ∀ n : ℕ, (g n).pt < (g (n+1)).pt,
intro, exact (h n).left,
exact increasing_by_step (λ n : ℕ, (g n).pt) h,
end

def restrict (f : [ℕ]² → color) (H : set ℕ) : [H]² → color :=
  λ h, f (⟨h.val, ⟨h.property.left, ⟨true.intro, true.intro⟩⟩⟩)

theorem infinite_ramsey_pairs_two_colors (f : [ℕ]² → color) :
  ∃ H : Inf, ∃ c : color,
  ∀ h : [H]²,
  (restrict f H) h = c :=
begin
  have hseq : ∃ (g : ℕ → condition f), initCond f << g 0 ∧ ∀ n, g n << g (n+1),
    exact exists_condition_seq f,
  cases hseq with g Hg,
  cases Hg with HgInit HgSeq,
  let g' := (λ n, (g n).pt),
  let f' := (λ n, project f (g' n) (g' (n+1))),
  have HgIncr : increasing g', exact cond_seq_incr f g HgSeq,
  let preH := (⟨image g' NatInf, incr_range_inf NatInf g' HgIncr⟩ : Inf),
  cases (pigeon_hole_principle f' preH) with Hred Hblue,

  any_goals { -- Red Case
    let H := (⟨reds f' preH, Hred⟩ : Inf),
    apply exists.intro (⟨image g' H, incr_range_inf H g' HgIncr⟩ : Inf),
    apply exists.intro red,
    intros p,
  },
  any_goals { -- Blue Case
    let H := (⟨blues f' preH, Hblue⟩ : Inf),
    apply exists.intro (⟨image g' H, incr_range_inf H g' HgIncr⟩ : Inf),
    apply exists.intro blue,
    intros p,
  },
  all_goals {
    have hp1 : p.val.fst ∈ image g' H, exact p.property.right.left,
    cases hp1 with h₁ Hh₁,
    have hfh₁ : f' h₁ = _, exact Hh₁.left.left,
    have hfgh₁ : project f (g' h₁) (g' (h₁+1)) = _, rw ←hfh₁,
    have hp2 : p.val.snd ∈ image g' H, exact p.property.right.right,
    cases hp2 with h₂ Hgh₂,
    have hg : p.val.fst < p.val.snd, exact p.property.left,
    rw [←Hh₁.right, ←Hgh₂.right] at hg,
    let d := h₂ - (h₁ + 1),
    have hd : h₂ = h₁ + d + 1,
      exact domain_dist_rw h₁ h₂ (incr_dom g' HgIncr h₁ h₂ hg),
    have stable :
      (project f (g' h₁)) (g' (h₁+1)) = (project f (g' h₁)) (g' (h₁+d+1)),
      exact cond_seq_stable_colors f g HgInit HgSeq h₁ d,
    rw [hfgh₁, ←hd, Hh₁.right, Hgh₂.right] at stable,
    have hproj : f ⟨p.val, _⟩ = project f p.val.fst p.val.snd,
      exact project_eq f ⟨p.val, ⟨p.property.left, trivial, trivial⟩⟩,
    rw [←stable, hproj] at hproj,
    rw ←hproj, refl,
  }
end

end ramsey_2_2
