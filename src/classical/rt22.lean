import classical.pigeon
import logic.basic

open set
open classical
open nat

section ramsey_2_2

local attribute [instance] prop_decidable

def infinite (H : set ℕ) := ∀ x : ℕ, ∃ y : ℕ, x < y ∧ H y

inductive color
| red : color
| blue : color

open color

-- bigNat is the set of Nats above a certain threshold
-- The intension was to use it when restricting a coloring
-- of pairs to a single color by choosing a first element
structure bigNat (m : ℕ) :=
(val : ℕ)
(pf : m < val)

def reds (f : ℕ → color) (H : set ℕ) := (λ n : ℕ, f n = red ∧ H n )
def blues (f : ℕ → color) (H : set ℕ) := (λ n : ℕ, f n = blue ∧ H n)

structure Inf :=
  (s : set ℕ)
  (pf : infinite s)

instance : has_coe Inf (set ℕ) := ⟨Inf.s⟩
instance : has_mem ℕ Inf := ⟨λ n H, n ∈ H.s⟩
instance : has_subset Inf := ⟨λ H₁ H₂, H₁.s ⊆ H₂.s⟩

lemma lt_succ : forall x y : ℕ, x < x + y + 1 :=
λ x y : ℕ, lt_add_of_pos_right x (succ_pos y)

-- cofinite sets are infinite
lemma cofinPrf (m : ℕ): infinite (λ n : ℕ, n > m) :=
begin
  intro n,
  apply exists.intro (n+m+1),
  constructor,
  rw add_assoc,
  apply lt_succ n m,
  rw [add_comm, ←add_assoc, add_comm],
  apply lt_add_of_pos_right,
  rw add_comm, apply succ_pos,
end

def cofin (m : ℕ) := Inf.mk (λ n : ℕ, n > m) (cofinPrf m)

-- Move a negation through a Π₂ formual
lemma neg_pi2 {p : ℕ → ℕ → Prop} :
  (¬ ∀ x : ℕ, ∃ y : ℕ, p x y) → ∃ x : ℕ, ∀ y : ℕ, ¬ p x y :=
begin
  intro h, rw ←not_forall_not,
  intro h', apply h, intro z,
  rw ←not_forall_not, exact (h' z)
end

-- This is a version of the PHP tailored to our use case
lemma pigeon_hole_principle (f : ℕ → color) (H : Inf):
infinite (reds f H) ∨ infinite (blues f H) :=
begin
  rw or_iff_not_imp_left,
  intros redFin,
  cases (neg_pi2 redFin) with w Hw, simp at Hw,
  intros x,
  have x_lt_a : x < x + w + 1, exact lt_succ x w,
  have w_lt_a : w < x + w + 1,
    { simp, exact lt_succ w x },
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
    { apply absurd (and.intro hRed Hb.right) (Hw b w_lt_b) },
    { exact ⟨hBlue, Hb.right⟩ }
  }
end

def sizeTwoSets (S : set ℕ) :=  {p : ℕ × ℕ // p.fst < p.snd ∧ S p.fst ∧ S p.snd}
notation `[ℕ]²` := sizeTwoSets univ
notation `[` S `]²` := sizeTwoSets S

def restr (f : [ℕ]² → color) (H : set ℕ) : [H]² → color :=
λ h, f (⟨h.val, ⟨h.property.left, ⟨true.intro, true.intro⟩⟩⟩)
infix `↾`:50 := restr


-- This is one possible way of restricting a coloring of
-- pairs to a first number. It comes with the cost of
-- having to keep track of the offeset.
def project (f : [ℕ]² → color) (x : ℕ) : ℕ → color :=
λ n : ℕ, f $ subtype.mk (x, x+n+1) ⟨lt_succ x n, trivial, trivial⟩

-- This is another way of restricting a coloring of
-- pairs to a first number. It comes with the cost of
-- not having a total coloring of ℕ
def project' (f : [ℕ]² → color) (m : ℕ) : bigNat m → color :=
λ n : bigNat m, f $ subtype.mk (m, n.val) ⟨n.pf, trivial, trivial⟩

def monochromatic (f : ℕ → color) (H : Inf) :=
  ∃ c : color, ∀ n, n ∈ H → f n = c

structure condition (f : [ℕ]² → color) extends Inf := (n : ℕ)
instance (f : [ℕ]² → color) : has_coe (condition f) Inf := ⟨λ c, ⟨c.s, c.pf⟩⟩

def ext {f : [ℕ]² → color} (p q: condition f) :=
  p.n < q.n ∧ q.n ∈ p.s ∧ q.s ⊆ p.s ∧ monochromatic (project f q.n) q

def ext' {f : [ℕ]² → color} (p q: condition f) :=
  p.n < q.n ∧ q.n + p.n + 1 ∈ p.s ∧ ∀ m : ℕ, q.s (m + q.n + 1) →  p.s (m + p.n + 1) ∧ monochromatic (project f q.n) q

infix `<<`:50 := ext

-- In this lemma, I can use project or project'.
-- It is proved here with project, but now
-- it is difficult to use it in order to obtain
-- a stable coloring.
lemma extend_cond (f : [ℕ]² → color) :
  ∀ (p : condition f), ∃ q : condition f, p << q :=
begin
  intros p,
  cases p.pf p.n with x Hx,
  have Hinf : infinite (reds (project f x) p.s) ∨ infinite (blues (project f x) p.s),
    apply pigeon_hole_principle,
  cases Hinf,
  apply exists.intro (condition.mk f ⟨reds (project f x) p.s, Hinf⟩ x),
  any_goals {apply exists.intro (condition.mk f ⟨blues (project f x) p.s, Hinf⟩ x)},
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
def iN : Inf := Inf.mk univ
begin
  intro x, apply exists.intro (x+1),
  constructor, apply lt_succ x 0, trivial,
end

-- Refiniment of a condition
def refine (f : [ℕ]² → color) :=
  Π (x : condition f), (λ (x : condition f), condition f) x

-- Used to create the sequence of conditions
def ext_seq (f : [ℕ]² → color) (ρ : refine f) : ℕ → condition f
| 0 := ρ ⟨f, iN, 0⟩
| (n+1) := let p := ext_seq n in ρ ⟨f, p, p.n⟩

def iter (f : [ℕ]² → color) (ρ : refine f) : ℕ → ℕ :=
  λ n : ℕ, (ext_seq f ρ n).n

-- I got stuck in a proof further down on this point,
-- and don't know how to proceed.
lemma silly (f : [ℕ]² → color) : ∀ p : condition f,
  p = {to_Inf := ↑p, n := p.n} :=
begin
  intro p,
  cases p, simp, sorry,
end

lemma iter_incr
  (f : [ℕ]² → color) (ρ : refine f)
  (x : ℕ) :
  (∀ (p : condition f), (λ (p q : condition f), p<<q) p (ρ p)) →
  (ext_seq f ρ x).n < (ext_seq f ρ (x+1)).n :=
begin
  intros hff,
  unfold ext_seq, simp,
  have h' : (ext_seq f ρ x) << ρ (ext_seq f ρ x),
    exact hff (ext_seq f ρ x),
  unfold ext at h',
  rewrite ←(silly f (ext_seq f ρ x)),
  exact h'.left,
end


def increasing (f : ℕ → ℕ) := ∀ x y : ℕ, x < y → f x < f y

lemma increasing_by_step (f : ℕ → ℕ) : (∀ n : ℕ, f n < f (n+1)) → increasing f :=
  λ (hf : ∀ n : ℕ, f n < f (n+1)) (x y : ℕ), nat.rec_on y
   (λ (contr : x < 0), absurd contr (nat.not_succ_le_zero x))
   (λ (z : ℕ) (ih : x < z → f x < f z) (h : x < nat.succ z),
   or.cases_on (nat.eq_or_lt_of_le (nat.le_of_lt_succ h))
   (λ hxz : x = z, hxz ▸ (hf x))
   (λ (hxz : x < z), nat.lt_trans (ih hxz) (hf z)))

-- Stable coloring definition
def stable (f : [ℕ]² → color) (g : ℕ → ℕ) : Prop :=
  ∀ x : ℕ, ∃ c : color, ∀ y : ℕ,
    x < y → g x < g y ∧ (project f (g x)) (g y) = c

lemma exists_stable (f : [ℕ]² → color) : ∃ (g : ℕ → ℕ),
  stable f g :=
begin
  have ac : ∃ (r : refine f),
    ∀ (p : condition f), (λ (p q : condition f), p<<q) p (r p),
  apply axiom_of_choice (extend_cond f),
  cases ac with ρ Hff,
  let g := λ m : ℕ, (ext_seq f ρ m).n,
  fapply exists.intro g,
  intros x,
  have h : (ext_seq f ρ x) << ρ (ext_seq f ρ x),
    apply Hff (ext_seq f ρ x),
  have h2 : ∀ p : condition f, p = ⟨f, ↑p, p.n⟩,
    intro p, cases p with H n, cases H with s pf, refl,
  have h3 : ρ (ext_seq f ρ x) = ext_seq f ρ (x+1),
    unfold ext_seq, simp, rw ← (h2 (ext_seq f ρ x)),
  rw h3 at h,
  have Hgx : g x < g (x+1), apply iter_incr f ρ x Hff,
  apply exists.intro (f ⟨(g x, g (x + 1)), Hgx, trivial, trivial⟩),
  intros y Hxy,
  constructor,
    apply increasing_by_step g,
    intro n, apply iter_incr f ρ n Hff, apply Hxy,
    sorry,
end


theorem rt22 (f : [ℕ]² → color) :
∃ H : Inf, ∃ c : color, ∀ h : [H]², (f↾H) h = c :=
sorry

end ramsey_2_2
