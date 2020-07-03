import algebra

variables {α : Type} (p q : α -> Prop)
variable a : α
variable r : Prop

namespace hidden
open classical

lemma true_conclusion (p q : Prop) : q -> p -> q :=
assume (hq : q) (hp : p),
show q, from hq

theorem false_implies (p q : Prop) : ¬ p -> (p -> q) :=
assume (hnp : ¬ p) (hp : p),
absurd hp hnp

example : (∀ x, p x ∧ q x) <-> (∀ x, p x) ∧ (∀ x, q x) :=
by {apply iff.intro,
		intro h,
		split; intro y;
		have hpqy := h y;
		cases hpqy with hp hq,
			exact hp, exact hq,
		intros h y,
		cases h with hfp hfq,
		exact ⟨hfp y, hfq y⟩}

example : (∀ x, p x -> q x) -> (∀ x, p x) -> (∀ x, q x) :=
by {intros hfpq hfp y,
	exact hfpq y (hfp y)}

example : (∀ x, p x) ∨ (∀ x, q x) -> ∀ x, p x ∨ q x :=
by {intros h y,
	apply h.elim;
	intros hp;
	have py := hp y,
		exact or.inl py,
		exact or.inr py}

example : α -> ((∀ x : α, r) <-> r) :=
by {intro y,
	apply iff.intro;
	intros,
		exact a y,
		exact a}

example : (∀ x, p x ∨ r) <-> (∀ x, p x) ∨ r :=
by {apply iff.intro;
	intros,
		apply (em r).elim;
		intro hr,
			right, exact hr,
			left, intro x, apply (a x).elim,
				intro px, exact px,
				intro hr, contradiction,

		cases a with hfp hr,
			left, exact hfp x,
			right, exact hr}

example : (∀ x, r -> p x) <-> (r -> ∀ x, p x) :=
iff.intro
	(assume (hfrp : ∀ x, r -> p x) (hr : r) (y : α),
	show p y, from hfrp y hr)
	(assume (hrfp : r → ∀ x, p x) (y : α) (hr : r),
	show p y, from hrfp hr y)

variables (men : Type) (barber : men)
variable (shaves : men -> men -> Prop)

theorem implies_and (p q r : Prop) : (p -> (q -> r)) <-> (p ∧ q -> r) :=
iff.intro
	(assume (hpqr : p -> q -> r) (hpq : p ∧ q),
	show r, from hpqr (hpq.left) (hpq.right))

	(assume (hpq : p ∧ q -> r) (hp : p) (hq : q),
	show r, from hpq (and.intro hp hq))

lemma not_and (p : Prop) : (p ∧ p -> false) -> p -> false :=
assume (hnpp : ¬ (p ∧ p)) (hp : p),
have hpp : p ∧ p, from (|hp, hp|),
absurd hpp hnpp

lemma prop_and_not (p : Prop) : ¬ (p <-> ¬ p) :=
assume hpenp : p <-> ¬ p,
have hpnp : p -> ¬ p, from hpenp.mp,
have hnpp : ¬ p -> p, from hpenp.mpr,
suffices hnp : ¬ p, from absurd (hnpp hnp) hnp,
have hppf : ¬ (p ∧ p), from (implies_and p p false).mp hpnp,
show ¬ p, from not_and p hppf

example (h : ∀ x : men, shaves barber x <-> ¬ shaves x x) : false := prop_and_not (shaves barber barber) (h barber)

namespace hidden
def divides (m n : ℕ) : Prop := ∃ k, m * k = n
instance : has_dvd nat := ⟨divides⟩
def even (n : ℕ) : Prop := 2 ∣ n
def prime (n : ℕ) : Prop := (n > 1) ∧ (∀ f : ℕ, f ∣ n -> f = 1 ∨ f = n)
def infinitely_many_primes : Prop := (∀ n : ℕ, prime n -> ∃ m : ℕ, (prime m) ∧ (m > n))
def Fermat_prime (n : ℕ) : Prop := prime n ∧ (∃ m : ℕ, n = 2 ^ (2 ^ m)+1)
def infinitely_many_Fermat_primes : Prop := (∀ n : ℕ, Fermat_prime n -> ∃ m : ℕ, (Fermat_prime m) ∧ (m > n))
def goldbach_conjecture : Prop := (∀ n : ℕ, even n ∧ n > 2 -> ∃ p q : ℕ, prime p ∧ prime q ∧ n = p + q)
def goldbach's_weak_conjecture : Prop :=
(∀ n : ℕ, n > 5 ∧ ¬(2 ∣ n) -> ∃ p q r : ℕ, prime p ∧ prime q ∧ prime r ∧ n = p + q + r)
def Fermat's_last_theorem : Prop := (∀ n : ℕ, n > 2 -> ¬(∃ a b c : ℕ, (a > 0 ∧ b > 0 ∧ c > 0)∧(a^n = b^n + c^n)))

variables (real : Type) [ordered_ring real]
variables (log exp : real -> real)
variable log_exp_eq : ∀ x, log (exp x) = x
variable exp_log_eq : ∀ {x}, x > 0 -> exp (log x) = x
variable exp_pos : ∀ x, exp x > 0
variable exp_add : ∀ x y, exp (x + y) = exp x * exp y
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]
example (y : real) (h : y > 0) : exp (log y) = y :=
exp_log_eq h
theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) : log (x * y) = log x + log y :=
calc
	log (x * y)	= log (exp (log x) * y)				: by rw exp_log_eq hx
		...		= log (exp (log x) * exp (log y))	: by rw exp_log_eq hy
		...		= log (exp (log x + log y))			: by rw exp_add (log x) (log y)
		...		= log x + log y						: by rw log_exp_eq (log x + log y)
end hidden

example (x : ℤ) : x * 0 = 0 :=
calc
	x * 0	= x * (x - x)	: by rw sub_self x
	...		= x * x - x * x	: by rw mul_sub x x x
	...		= 0				: by rw sub_self (x*x)

theorem not_not (hnnr : ¬¬r) : r :=
by_contradiction
	(assume hnr : ¬ r,
	absurd hnr hnnr)

include a
example : (∃ x : α, r) <-> r :=
by {apply iff.intro;
	intros s,
		cases s with x hr, exact hr,
		constructor, exact a, exact s}

example : (∃ x : α, p x ∧ r) <-> (∃ x, p x) ∧ r :=
by {apply iff.intro;
	intros he;
	cases he with hep hpr,
		constructor,
			constructor, exact hpr.left, exact hpr.right,
		cases hep with y py,
		constructor, exact and.intro py hpr}

example : (∃ x, p x ∨ q x) <-> (∃ x, p x) ∨ (∃ x, q x) :=
by {apply iff.intro;
	intros h,
	cases h with h1 h2,
		cases h2,
			left, constructor, exact h2,
			right, constructor, exact h2,
	cases h;
	cases h with x h1;
	constructor,
		left, exact h1,
		right, exact h1}

local attribute [instance] classical.prop_decidable
example : (∀ x, p x) <-> ¬ (∃ x, ¬ p x) :=
by {apply iff.intro,
		intros hfp henp,
		cases henp with w npw,
		have := hfp w,
		contradiction,

		intros h x,
		by_contra hnpx,
		have := exists.intro x hnpx,
		contradiction}


theorem not_exists : (¬ ∃ x, p x) <-> (∀ x, ¬ p x) :=
by {apply iff.intro,
		intros hnep x hpx,
		have := exists.intro x hpx,
		contradiction,

		intros ha hb,
		cases hb with w hpw,
		have := ha w,
		contradiction}

theorem not_forall : (¬ ∀ x, p x) <-> (∃ x, ¬ p x) :=
by {apply iff.intro,
		intros hnfp,
		by_contra hnenp,
			suffices hfp : ∀ (x : α), p x, from hnfp hfp,
			intro x,
			by_contra hnpx,
				have := exists.intro x hnpx,
				contradiction,

		intros henp hfp,
		cases henp with w hnpw,
		have := hfp w,
		contradiction}

example : (∃ x, p x) <-> ¬ (∀ x, ¬ p x) :=
by {apply iff.intro,
		intros hep hfnp,
		cases hep with w hpw,
		have := hfnp w,
		contradiction,

		intro hnfnp,
		by_contra hnep,
		have := (not_exists p a).mp hnep,
		contradiction}

example : (∀ x, p x -> r) <-> (∃ x, p x) -> r :=
by {apply iff.intro,
		intros hfpr hep,
		cases hep with w hpw,
		exact hfpr w hpw,

		intros hepr x hpx,
		have := exists.intro x hpx,
		exact hepr this}



theorem contra (p q : Prop) : (p -> q) -> (¬ q -> ¬ p) :=
assume (hpq : p -> q) (hnq : ¬ q) (hp : p),
absurd (hpq hp) hnq

theorem notC_notH (p q : Prop) : ¬ q -> (p -> q) -> ¬ p :=
by {intros hnq hpq hp,
	have := hpq hp,
	contradiction}

example : (∃ x, p x -> r) <-> (∀ x, p x) -> r := 
by {apply iff.intro,
		intros hepr hfp,
		cases hepr with w hpwr,
		exact (hpwr (hfp w)),

		intros hfpr,
		apply (em r).elim;
		intro hr,
			have := (true_conclusion (p a) r hr),
			exact exists.intro a this,

			have h := notC_notH (∀ (x : α), p x) (∀ (x : α), p x) r hr hfpr,
			have := (not_forall p a).mp h,
			cases this with w hnpw,
			have := false_implies (p w) r hnpw,
			exact exists.intro w this}

example : (∃ x, r -> p x) <-> (r -> ∃ x, p x) := 
by {apply iff.intro,
		intros herp hr,
		cases herp with w hrpw,
		exact exists.intro w (hrpw hr),

		intro hrep,
		apply (em r).elim;
		intro hr,
			cases (hrep hr) with w hpw,
			constructor, exact (true_conclusion r (p w) hpw),

			have hrpa := false_implies r (p a) hr,
			constructor, exact hrpa}

example:(∃ x, (p x ∧ ∀ y, (p y → y = x)))
		<-> ∃ x, p x ∧ ∀ y y1, (p y ∧ p y1 → y = y1) :=
by {apply iff.intro;
		intro h;
		cases h with w hw;
		cases hw with hpw hf;
		constructor,
			split, exact hpw,
			intros y y1 h,
			have hyw := hf y h.left,
			have hy1w := hf y1 h.right,
			rw hyw, rw hy1w,

			split, exact hpw,
			intros y hpy,
			have := and.intro hpy hpw,
			exact hf y w this}
end hidden