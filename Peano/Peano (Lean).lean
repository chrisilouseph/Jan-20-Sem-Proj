import tactic-- For tactics like use, replace, conv_lhs and rintros

-- The data type implementing the natural numbers
-- with Zero and the successor function S
inductive Peano
| Zero  : Peano
| S     : Peano → Peano

namespace Peano
-- Opening the namespace prevents name clashes with pre-defined lemmas and theorems for ℕ

-- Verification of Peano's Axioms:

/-
Axioms 1 (Zero being a natural number) & 2 (existence of the successor function)
are clearly satisfied by the definition of the type Peano

Axiom 3: The successor function is injective.

For all inductive datatypes, Lean considers the constructor functions to be injective
For Peano in particular, Lean gives us the theorem S.inj
-/
lemma PA3 : ∀ p q, S p = S q → p = q := @S.inj

/-
Axiom 4: Zero is not the successor of any number.

Lean considers the constructor functions to be mutually injective too,
i.e. different constructors of an inductive type
cannot produce equal terms, given by Peano.no_confusion
-/
lemma PA4 : ¬ ∃ n, S n = Zero := λ ⟨w, h⟩, Peano.no_confusion h

/-
Axiom 5: Any set A satisfying the following properties is equal to the ℕ:
a) 0 ∈ A and b) If x ∈ A, then S x ∈ A.

Lean defines an inductive principle for each inductive type
called rec_on. For Peano, we have the function

Peano.rec_on : ∀ {C : Peano → Sort u_1} (n : Peano), C Zero → (∀ (a : Peano), C a → C (S a)) → C n

Given n of type Peano, Peano.rec_on constructs an element, C n, of some type
given the image of Zero, C Zero, and the image of (S a) given the image of an arbitrary Peano a.

A note about the lemmas proved in the Lean library used in the next proof:
subset.antisymm : ∀ {α : Type} {a b : set α}, a ⊆ b → b ⊆ a → a = b
subset_univ : ∀ {α : Type} (s : set α), s ⊆ univ
-/
open set
lemma PA5 (A : set Peano) (h : Zero ∈ A ∧ ∀ n, n ∈ A → S n ∈ A) : A = univ :=
subset.antisymm (subset_univ _) (λ p _, Peano.rec_on p h.left h.right)

-- Now some basic arithmetic will be developed using Peano.

-- Proving that equality is decidable for Peano
instance decidable_eq : ∀ p q : Peano, decidable (p = q)
| Zero  Zero    := is_true rfl
| Zero  (S q)   := is_false (λ hw, Peano.no_confusion hw)
| (S p) Zero    := is_false (λ hw, Peano.no_confusion hw)
| (S p) (S q)   :=
  match decidable_eq p q with
  | is_true h := is_true (h ▸ rfl)
  | is_false h := is_false (λ hw, h $ S.inj hw)
  end

variables p q r : Peano
-- To prevent having to introduce variables for each lemma

-- Defining addition by cases of the first argument
def add : Peano → Peano → Peano
| Zero := id
| (S p) := S ∘ (add p)  -- Curried constructing function

infix + := add
-- add a b = a + b

-- Definitionally equivalent expressions can be shown to be equal by rfl
lemma zero_add : Zero + p = p := rfl
lemma succ_eq_add_one : S p = Zero.S + p := rfl
lemma succ_add : p.S + q = (p + q).S := rfl

-- More complicated theorems usually involve induction with rewrites
-- Subgoals like the base case of a proof by induction are enclosed in {}
lemma add_succ : p + q.S = (p + q).S :=
begin
  induction p with p hi,
    { refl },
  rw [succ_add, succ_add, hi]
end

lemma succ_comm : p.S + q = p + q.S := by rw [succ_add, add_succ]

lemma add_zero : p + Zero = p :=
begin
  induction p with p hi,
    { refl  },
  rw [succ_add, hi]
end

lemma add_comm : p + q = q + p :=
begin
  induction p with p hi,
    { rw [zero_add, add_zero] },
  rw [succ_add, add_succ, hi]
end

lemma add_assoc : p + q + r = p + (q + r) :=
begin
  induction p with p hi,
    { refl },
  repeat {  rw succ_add },
  rw hi
end

lemma add_left_cancel_iff : p + q = p + r ↔ q = r :=
begin
  split;
  intro h,
  { induction p with p hi,
    { exact h  },
    rw [succ_add, succ_add] at h,
    injection h with h1,
    exact hi h1 },
  rw h
end

lemma add_right_cancel_iff : p + q = r + q ↔ p = r :=
by rw [add_comm, add_comm r, add_left_cancel_iff]

lemma add_eq_zero_iff : p + q = Zero ↔ p = Zero ∧ q = Zero :=
begin
  split;
  intro h,
  { suffices heq : p = Zero,
    { use heq,
      rwa [heq] at h  },
    cases p,
    { refl  },
    injections  },
  rw [h.left, h.right, zero_add]
end

-- Defining multiplication
def mul : Peano → Peano → Peano
| Zero     b := Zero
| (S p) b := b + mul p b

infix * := mul
-- mul a b = a * b

-- Basic multiplication identities
lemma zero_mul : Zero * p = Zero := rfl
lemma succ_mul : p.S * q = q + p * q := rfl
lemma one_mul : Zero.S * p = p := by rw [succ_mul, zero_mul, add_zero]

lemma mul_succ : p * q.S = p + p * q :=
begin
  induction p with p hi,
  { refl },
  rw [succ_mul, succ_mul, hi, ←add_assoc, ←add_assoc],
  rw [add_comm q.S, succ_add, add_succ]
end

lemma mul_zero : p * Zero = Zero :=
begin
  induction p with p hi,
  { refl },
  rw [succ_mul, hi, add_zero]
end

lemma mul_comm : p * q = q * p :=
begin
  induction p with p hi,
  { rw [mul_zero, zero_mul] },
  rw [mul_succ, succ_mul, hi]
end

lemma mul_one : p * Zero.S = p := by rw [mul_comm, one_mul]

lemma mul_add : p * (q + r) = p * q + p * r :=
begin
  induction p with p hi,
  { refl },
  repeat {  rw succ_mul },
  rw [hi, add_assoc, add_assoc, ←add_assoc r, ←add_assoc _ r, add_comm r]
end

lemma add_mul : (p + q) * r = p * r + q * r := by repeat {rw mul_comm _ r}; rw mul_add

lemma mul_assoc : p * q * r = p * (q * r) :=
begin
  induction p with p hi,
  { refl  },
  repeat {  rw succ_mul },
  rw [add_mul, hi]
end

lemma mul_eq_zero_iff {p q : Peano} : p * q = Zero ↔ p = Zero ∨ q = Zero :=
begin
  split,
  { induction p with p hi,
    { exact imp_intro (or.inl rfl)},
    intro h,
    rw [succ_mul, add_eq_zero_iff] at h,
    exact or.inr h.left},
  rintro (rfl | rfl),
  { refl  },
  rw mul_zero
end

lemma mul_eq_one_iff {p q : Peano} : p * q = Zero.S ↔ p = Zero.S ∧ q = Zero.S :=
begin
  split;
  intro h,
  { suffices heq : q = Zero.S,
    { rw [heq, mul_one] at h,
      tauto  },
    cases p,
    { rw zero_mul at h,
      injections  },
    cases q,
    { rwa mul_zero at h },
    rw [succ_mul, succ_add] at h,
    injection h with h1,
    rw add_eq_zero_iff at h1,
    rw h1.left  },
  rw [h.left, h.right, one_mul]
end

-- Defining order
def le := ∃ d, q = d + p
def lt := le p.S q

instance : has_le Peano := ⟨le⟩ -- To be able to use ≤ and ≥ notation
instance : has_lt Peano := ⟨lt⟩ -- To be able to use < and > notation

-- Basic ≤ lemmas
lemma zero_min : Zero ≤ p := ⟨p, (add_zero p).symm⟩
lemma le_succ : p ≤ p.S := ⟨Zero.S, rfl⟩
lemma lt_succ : p < p.S := ⟨Zero, rfl⟩
lemma le_refl : p ≤ p := ⟨Zero, rfl⟩

lemma le_trans {p q r : Peano} : p ≤ q → q ≤ r → p ≤ r
| ⟨pq, hpq⟩ ⟨qr, hqr⟩ := ⟨qr + pq, by rwa [add_assoc, ←hpq]⟩

lemma le_antisymm {p q : Peano} : p ≤ q → q ≤ p → p = q :=
begin
  rintro ⟨pq, hpq⟩ ⟨qp, hqp⟩,
  rw [←zero_add p, hpq, ←add_assoc, add_right_cancel_iff, eq_comm, add_eq_zero_iff] at hqp,
  rw [hpq, hqp.right, zero_add]
end

lemma le_zero : p ≤ Zero ↔ p = Zero :=
⟨λ h, le_antisymm h $ zero_min _, λ hp, hp ▸ le_refl _⟩

lemma not_succ_le_zero : ¬ S p ≤ Zero :=
λ ⟨d, hd⟩, by rw add_succ at hd; injections

lemma succ_le_succ_iff {p q : Peano} : p ≤ q ↔ p.S ≤ q.S :=
⟨λ ⟨d, hd⟩, ⟨d, by rw [hd, add_succ]⟩,
λ ⟨d, hd⟩, ⟨d, by rw [add_succ] at hd; exact S.inj hd⟩⟩

lemma le_total : p ≤ q ∨ q ≤ p :=
begin
  induction q with q hi,
  { exact or.inr (zero_min _)  },
  rcases hi with hi | ⟨_ | d, rfl⟩,
    { exact or.inl (le_trans hi (le_succ _)) },
  { exact or.inl (le_succ _) },
  exact or.inr ⟨d, succ_comm _ _⟩,
end

lemma add_le_add {p q r s : Peano} : p ≤ r → q ≤ s → p + q ≤ r + s
| ⟨dpr, h1⟩ ⟨dqs, h2⟩ :=
⟨dpr + dqs, by rw [h1, h2, add_assoc, ←add_assoc p, add_comm p, add_assoc, ←add_assoc]⟩

lemma mul_left_le {p q r : Peano} : p ≤ q → r * p ≤ r * q
| ⟨d, hd⟩ := ⟨r*d, by rw [hd, mul_add]⟩

-- Basic < lemmas
lemma lt_irrefl : ¬ p < p :=
begin
  rintro ⟨d, hd⟩,
  conv_lhs at hd {  rw ←zero_add p  },
  rw [←succ_comm, add_right_cancel_iff] at hd,
  injections
end

lemma lt_iff_le_not_le : p < q ↔ p ≤ q ∧ ¬q ≤ p :=
begin
  split,
  { intro h,
    have hpq := le_trans (le_succ _) h,
    use hpq,
    intro hw,
    replace hpq := le_antisymm hw hpq,
    rw hpq at h,
    exact lt_irrefl _ h },
  rintro ⟨⟨_ | d, rfl⟩, h⟩,
    { have := le_refl p,
      contradiction },
  rw succ_comm,
  use d
end

-- Proving that < and ≤ defined above form a total order on Peano
instance le_order : linear_order Peano :=
{ le := le,
  le_refl := le_refl,
  le_trans := @le_trans,
  le_antisymm := @le_antisymm,
  le_total := le_total,
  lt := lt,
  lt_iff_le_not_le := lt_iff_le_not_le  }

-- Proving that < and ≤ are decidable for Peano
instance decidable_le : ∀ p q : Peano, decidable (p ≤ q)
| Zero  _ := is_true (zero_min _)
| (S p) Zero := is_false (not_succ_le_zero _)
| (S p) (S q) :=
  match decidable_le p q with
  | is_true h := is_true (succ_le_succ_iff.mp h)
  | is_false h := is_false (λ hw, h $ succ_le_succ_iff.mpr hw)
  end

instance decidable_lt : ∀ p q : Peano, decidable (p < q) :=
λ p q, Peano.decidable_le (p.S) q

-- the pred function
def P : Peano → Peano
| Zero := Zero
| (S p) := p
/-
Defining P Zero = Zero is more convenient than throwing an exception.
Similarly, whenever a ≤ b, a - b will be defined as Zero
when subtraction is defined later.
To prevent contradictions due to these edge cases,
an extra hypothesis will be added to the concerned theorems
-/

-- Basic pred lemmas

lemma pred_zero : P Zero = Zero := rfl
lemma P_of_S : P (S p) = p := by rw P

lemma S_of_P : S (P Zero) = Zero.S ∧ ∀ p ≠ Zero, S (P p) = p :=
⟨rfl, λ p, Peano.cases_on p (λ hpp, absurd rfl hpp) (λ _ _, rfl)⟩

lemma P_eq_zero : P p = Zero ↔ p = Zero ∨ p = Zero.S :=
begin
  split,
  { intro h,
    rcases p with _ | _ | p,
      { exact or.inl rfl  },
    { exact or.inr rfl  },
    rw P_of_S at h,
    contradiction},
  rintro (rfl | rfl);
    { refl  },
end

lemma add_P (hq : q ≠ Zero) : p + P q = P (p + q) :=
begin
  induction p with p hi,
  { refl  },
  rw [succ_add, succ_add, hi, P_of_S, S_of_P.right],
  intro h,
  cases (add_eq_zero_iff _ _).mp h,
  contradiction
end

-- Defining subtraction
def sub : Peano → Peano → Peano
| p     Zero := p
| p (S q) := P (sub p q)

infix - := sub -- sub p q = p - q

-- Basic subtraction lemmas
lemma sub_zero : p - Zero = p := rfl
lemma sub_one : p - Zero.S = P p := rfl
lemma succ_sub_one : S p - Zero.S = p := rfl
lemma sub_succ : p - S q = P (p - q) := rfl

lemma zero_sub : Zero - p = Zero :=
begin
  induction p with p hi,
  { refl },
  rw [sub_succ, hi, pred_zero]
end

lemma succ_sub_succ : S p - S q = p - q :=
begin
  induction q with q hi,
  { refl  },
  rw [sub_succ, hi, sub_succ]
end

lemma sub_self : p - p = Zero :=
begin
  induction p with p hw,
  { refl  },
  rwa succ_sub_succ
end

lemma add_sub_cancel : p + q - q = p :=
begin
  induction q with q hi,
  { rw [add_zero, sub_zero] },
  rwa [add_succ, succ_sub_succ],
end

lemma sub_add : p - (q + r) = p - q - r :=
begin
  induction r with r hi,
  { rw [add_zero, sub_zero] },
  rw [add_succ, sub_succ, sub_succ, hi]
end

lemma sub_eq_iff_eq_add (hpq : p ≥ q) : p - q = r ↔ p = r + q :=
begin
  split;
  rintro rfl,
  { rcases hpq with ⟨d, rfl⟩,
    rw add_sub_cancel  },
  rw add_sub_cancel
end

lemma sub_eq_zero_iff {p q : Peano} : p ≤ q ↔ p - q = Zero :=
begin
  induction q with q hi,
  { rw [le_zero p, sub_zero]  },
  split,
  { rintro ⟨d, hd⟩,
    rw [hd, add_comm, sub_add, sub_self, zero_sub]  },
  intro h,
  rw [sub_succ, P_eq_zero] at h,
  cases h,
  { exact le_trans (hi.mpr h) (le_succ _) },
  rw sub_eq_iff_eq_add at h,
  { use [Zero, h.symm]  },
  cases le_total q p with h1 h2,
  { exact h1  },
  rw [hi, h] at h2,
  contradiction
end

lemma add_sub_assoc {p q r : Peano} (h : r ≤ q) : p + (q - r) = p + q - r :=
begin
  induction r with r hi,
  { refl },
  rw [sub_succ, sub_succ, ←hi (le_trans (le_succ r) h), add_P],
  intro hw,
  rw ←sub_eq_zero_iff at hw,
  replace hw := le_trans h hw,
  replace h := lt_succ r,
  rw lt_iff_not_ge at h,
  contradiction
end

lemma sub_add_comm {p q r : Peano} (h : q ≤ p) : p - q + r = p + r - q :=
by rw [add_comm, add_sub_assoc h, add_comm]

lemma mul_sub : p * (q - r) = p * q - p * r :=
begin
  induction p with p hi,
  { refl  },
  cases le_total q r with h h,
  { rw [sub_eq_zero_iff.mp h, mul_zero, eq_comm, sub_eq_zero_iff.mp],
    exact mul_left_le h },
  repeat {  rw succ_mul },
  rw [hi, sub_add, add_sub_assoc (mul_left_le h), sub_add_comm h]
end

lemma sub_mul : (p - q) * r = p * r - q * r := by repeat {rw mul_comm _ r}; rw mul_sub

lemma mul_left_cancel_iff {p q r : Peano} (hp : p ≠ Zero) : (p * q = p * r ↔ q = r) :=
begin
  split;
  intro h,
  { cases (le_antisymm_iff.mp h) with h1 h2,
    rw [sub_eq_zero_iff, ←mul_sub, mul_eq_zero_iff, ←sub_eq_zero_iff] at h1 h2,
    exact le_antisymm (or.resolve_left h1 hp) (or.resolve_left h2 hp) },
  rw h
end

lemma mul_right_cancel_iff (hq : q ≠ Zero) : (p * q = r * q ↔ p = r) :=
by rw [mul_comm, mul_comm r, mul_left_cancel_iff hq]

-- Defining divisibility
def dvd := ∃ f, q = f * p
infix ∣ := dvd -- dvd a b = a ∣ b

-- Basic divisibility lemmas
lemma dvd_refl : p ∣ p := ⟨Zero.S, (one_mul p).symm⟩

lemma dvd_trans {p q r : Peano} : p ∣ q → q ∣ r → p ∣ r
| ⟨f, hpq⟩ ⟨g, hqr⟩ := ⟨g*f, by rwa [mul_assoc, ←hpq]⟩

lemma dvd_zero : p ∣ Zero := ⟨Zero, (zero_mul p).symm⟩
lemma dvd_mul_right (h : p ∣ q) : p ∣ q * r := dvd_trans h ⟨r, mul_comm _ _⟩
lemma dvd_mul_left (h : p ∣ q) : p ∣ r * q := dvd_trans h ⟨r, rfl⟩

lemma dvd_antisymm {p q : Peano} : p ∣ q → q ∣ p → p = q := 
begin
  rintros ⟨f, hab⟩ ⟨g, rfl⟩,
  cases q,
  { rw mul_zero },
  conv_lhs at hab { rw ←one_mul q.S },
  rw [←mul_assoc, mul_right_cancel_iff, eq_comm, mul_eq_one_iff] at hab,
  { rw [hab.right, one_mul] },
  intro,
  injections
end

lemma dvd_add_iff_left {p q r : Peano} : p ∣ q → (p ∣ r ↔ p ∣ q + r)
| ⟨f1, hf1⟩ :=
  ⟨λ ⟨f2, hf2⟩, ⟨f1+f2, by rw [add_mul, hf1, hf2]⟩,
  λ ⟨f2, hf2⟩, ⟨f2-f1, by rw [sub_mul, ←hf1, ←hf2, add_comm, add_sub_cancel]⟩⟩

lemma dvd_add_iff_right {p q r : Peano} (h : p ∣ q) : (p ∣ r ↔ p ∣ r + q) :=
by rw [add_comm, dvd_add_iff_left h]

lemma dvd_one : p ∣ Zero.S ↔ p = Zero.S :=
⟨λ ⟨f, hf⟩, (mul_eq_one_iff.mp hf.symm).right, λ h, h ▸ dvd_refl p⟩

lemma zero_dvd : Zero ∣ p ↔ Zero = p :=
⟨λ ⟨f, hf⟩, mul_zero f ▸ hf.symm, λ h, h ▸ dvd_refl _⟩

lemma dvd_of_mul_dvd_mul_left {p q r : Peano} (hp : p ≠ Zero) : p * q ∣ p * r → q ∣ r :=
λ ⟨f, hf⟩, ⟨f, (mul_left_cancel_iff hp).mp
(by rwa [←mul_assoc, mul_comm p f, mul_assoc])⟩

lemma dvd_of_mul_dvd_mul_right {p q r : Peano} (hq : q ≠ Zero) : p * q ∣ r * q → p ∣ r :=
by rw [mul_comm, mul_comm r]; apply dvd_of_mul_dvd_mul_left hq

-- Proving that ∣ forms a partial order on Peano
instance div_order : partial_order Peano :=
{ le := dvd,
  le_refl := dvd_refl,
  le_trans := @dvd_trans,
  le_antisymm := @dvd_antisymm  }

end Peano