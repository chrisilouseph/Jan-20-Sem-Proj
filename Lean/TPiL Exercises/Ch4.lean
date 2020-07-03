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
iff.intro
	(assume (h : ∀ x, p x ∧ q x),
	have hfp : ∀ x, p x, from assume (y : α), (h y).left,
	suffices hfq : ∀ x, q x, from and.intro hfp hfq,
	show ∀ x, q x, from assume (y : α), (h y).right)

	(assume (hfpq : (∀ x, p x) ∧ (∀ x, q x)) (y : α),
	show p y ∧ q y, from (|hfpq.left y, hfpq.right y|))

example : (∀ x, p x -> q x) -> (∀ x, p x) -> (∀ x, q x) :=
assume (hfpq : ∀ x, p x -> q x) (hfp : ∀ x, p x) (y : α),
have hpq : p y -> q y, from hfpq y,
have hp : p y, from hfp y,
show q y, from hpq hp

example : (∀ x, p x) ∨ (∀ x, q x) -> ∀ x, p x ∨ q x :=
assume (hfpq : (∀ x, p x) ∨ (∀ x, q x)) (y : α),
hfpq.elim
	(assume : ∀ x, p x,
	show p y ∨ q y, from or.inl (this y))
	(assume : ∀ x, q x,
	show p y ∨ q y, from or.inr (this y))

example : α -> ((∀ x : α, r) <-> r) :=
assume y : α,
iff.intro
	(assume : ∀ x : α, r,
	show r, from this y)
	(assume (hr : r) (y : α),
	show r, from hr)

example : (∀ x, p x ∨ r) <-> (∀ x, p x) ∨ r :=
iff.intro
	(assume (hfpr : ∀ x, p x ∨ r),
	(em r).elim
		(assume hr : r, or.inr hr)
		(assume hnr : ¬ r,
		suffices hfp : ∀ x, p x, from or.inl hfp,
		assume y : α,
		(hfpr y).elim
			(assume hpy : p y, hpy)
			(assume hr : r, absurd hr hnr)
		))
	(assume (hfpr : (∀ x, p x) ∨ r) (y : α),
	hfpr.elim
		(assume : ∀ x, p x,
		show p y ∨ r, from or.inl (this y))
		(assume : r,
		show p y ∨ r, from or.inr this))

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

example : ¬ ∀ (α : Type) (r : Prop), r → (∃ x : α, r) :=
begin
  intro h,
  cases h empty _ true.intro with w,
  cases w
end

example : (∃ x : α, r) <-> r :=
iff.intro
	(assume her : ∃ x : α, r,
	exists.elim her
		(assume (w : α) (hr : r),
		show r, from hr))

	(assume (hr : r),
	show ∃ x : α, r, from ⟨a, hr⟩ )

example : (∃ x : α, p x ∧ r) <-> (∃ x, p x) ∧ r :=
iff.intro
	(assume ⟨(w : α) , (hpw : p w), (hr : r)⟩, ⟨⟨w, hpw⟩, hr⟩)

	(assume hepr : (∃ x, p x) ∧ r,
	match hepr.left with (|(w : α), (hw : p w)|) := ⟨ w, hw, hepr.right⟩ 
	end)

example : (∃ x, p x ∨ q x) <-> (∃ x, p x) ∨ (∃ x, q x) :=
iff.intro
	(assume hepq : ∃ x, p x ∨ q x,
	match hepq with (|(w : α), (hw : p w ∨ q w)|) :=
		hw.elim
			(assume hp : p w,
			suffices hep : ∃ x, p x, from or.inl hep,
			show ∃ x, p x, from (|w, hp|))
			(assume hq : q w,
			suffices heq : ∃ x, q x, from or.inr heq,
			show ∃ x, q x, from (|w, hq|))
	end)

	(assume hepeq : (∃ x, p x) ∨ (∃ x, q x),
	hepeq.elim
		(assume hep : ∃ x, p x,
		match hep with (|(w : α), (hw : p w)|) := (|w, or.inl hw|)
		end)
		(assume heq : ∃ x, q x,
		match heq with (|(w : α), (hw : q w)|) := (|w, or.inr hw|)
		end))

example : (∀ x, p x) <-> ¬ (∃ x, ¬ p x) :=
iff.intro
	(assume (hfp : ∀ x, p x) (|(w : α), (hw : ¬ p w)|),
	absurd (hfp w) hw)

	(assume (hnenp : ¬ (∃ x, ¬ p x)) (y : α),
	by_contradiction
		(assume hnp : ¬ p y,
		have henp : ∃ x, ¬ p x, from (|y, hnp|),
		show false, from hnenp henp))

theorem not_exists : (¬ ∃ x, p x) <-> (∀ x, ¬ p x) :=
iff.intro
	(assume (hnep : ¬ ∃ x, p x) (y : α),
	classical.by_contradiction
		(assume hnnpy : ¬ ¬ p y,
		have hpy : p y, from not_not (p y) hnnpy,
		have ∃ x, p x, from ⟨y, hpy⟩,
		absurd this hnep))

	(assume (hnp : ∀ x, ¬ p x) (hep : ∃ x, p x),
	match hep with (|w, hw|) := absurd hw (hnp w) end)

theorem not_forall : (¬ ∀ x, p x) <-> (∃ x, ¬ p x) :=
iff.intro

	(assume hnfp : (¬ ∀ x, p x),
	classical.by_contradiction
		(assume hnenp : ¬ ∃ x, ¬ p x,
		suffices hfp : ∀ x, p x, from absurd hfp hnfp,
		assume y : α,
		classical.by_contradiction
			(assume hnpq : ¬ p y,
			have ∃ x, ¬ p x, from ⟨y, hnpq⟩,
			absurd this hnenp)
		))

	(assume (henp : ∃ x, ¬ p x) (hfp : ∀ x, p x),
	match henp with (|w, (hw : ¬ p w)|) := absurd (hfp w) hw end)

example : (∃ x, p x) <-> ¬ (∀ x, ¬ p x) :=
iff.intro
	(assume (|w, (hw : p w)|) (hfnp : ∀ x, ¬ p x),
	absurd hw (hfnp w))

	(assume (hnfnp : ¬ (∀ x, ¬ p x)),
	by_contradiction
		(assume hnep : ¬ (∃ x, p x),
		have hfnp : ∀ x, ¬ p x, from (not_exists p).mp hnep,
		show false, from hnfnp hfnp))

example : (∀ x, p x -> r) <-> (∃ x, p x) -> r :=
iff.intro
	(assume (hfpr : ∀ x, p x -> r) (hep : ∃ x, p x),
	match hep with (|w, (hw : p w)|) := hfpr w hw end)

	(assume (hepr : (∃ x, p x) -> r) (y : α),
	(em (∃ x, p x)).elim
		(assume hep : ∃ x, p x,
		have hr : r, from hepr hep,
		show p y -> r, from true_conclusion (p y) r hr)

		(assume hnep : ¬ ∃ x, p x,
		have hfnp : ∀ x, ¬ p x, from (not_exists p).mp hnep,
		have hnp : ¬ p y, from hfnp y,
		show p y -> r, from false_implies (p y) r hnp))

example : (∃ x, p x -> r) <-> (∀ x, p x) -> r := 
iff.intro
	(assume (hepr : ∃ x, p x -> r) (hfp : ∀ x, p x),
	match hepr with (|w, (hw : p w -> r)|) :=
		show r, from hw (hfp w)
	end)

	(assume (hfpr : (∀ x, p x) -> r),
	(em (∀ x , p x)).elim
		(assume hfp : ∀ x, p x,
		have hr : r, from hfpr hfp,
		show ∃ x, p x -> r, from (|a, true_conclusion (p a) r hr|))

		(assume hnfp : ¬ ∀ x, p x,
		have henp : ∃ x, ¬ p x, from (not_forall p).mp hnfp,
		match henp with ⟨ (w : α), (hw : ¬ p w)⟩ := ⟨ w, false_implies (p w) r hw⟩ end))

example : (∃ x, r -> p x) <-> (r -> ∃ x, p x) := 
iff.intro
	(assume (herp : ∃ x, r -> p x) (hr : r),
	match herp with (|w, (hw : r -> p w)|) := (|w, hw hr|) end)

	(assume (hrep : r -> ∃ x, p x),
	(em r).elim
		(assume hr : r,
		match (hrep hr) with ⟨w, hpw⟩ := ⟨w, true_conclusion r (p w) hpw⟩ end)
		(assume (hnr : ¬ r),
		show ∃ x, r -> p x, from (|a, false_implies r (p a) hnr|)))

end hidden