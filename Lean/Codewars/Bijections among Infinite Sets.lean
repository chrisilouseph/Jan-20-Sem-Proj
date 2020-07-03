import data.nat.parity tactic
open function
set_option pp.beta true

/-
Introduction to bijection, cardinality, and infinite sets
Problem by solitude
(https://www.codewars.com/kata/5ca3fcc8f7fb0800201ba88f)

The isomorphism structure between two types A and B given below includes four fields:
  • a function a_to_b : A → B
  • a function b_to_a : B → A
  • a proof that b_to_a is the left inverse of a_to_b
  • a proof that b_to_a is the right inverse of a_to_b

Note :  While proving two types are `iso`, we use `def` instead of `theorem`
        because iso is a structure and not a Prop
-/

structure iso (A : Type) (B : Type) :=
  (a_to_b : A → B)
  (b_to_a : B → A)
  (a_b_a : ∀ a, b_to_a (a_to_b a) = a)
  (b_a_b : ∀ b, a_to_b (b_to_a b) = b)

-- Task 1
-- General properties of iso

-- Task 1-1 : Prove that any set has the same cardinality as itself
def iso_rfl {A : Type} : iso A A := 
{
  a_to_b := id,
  b_to_a := id,
  a_b_a := λ x, rfl,
  b_a_b := λ x, rfl,
}

-- Task 1-2 : Prove that iso is symmetric
def iso_symm {A B : Type} (i : iso A B) : iso B A :=
{
  a_to_b := i.b_to_a,
  b_to_a := i.a_to_b,
  a_b_a := i.b_a_b,
  b_a_b := i.a_b_a,
}

-- Task 1-3 : Prove that iso is transitive
def iso_trans {A B C : Type} (ab : iso A B) (bc : iso B C) : iso A C :=
{
  a_to_b := λ a, bc.a_to_b (ab.a_to_b a),
  b_to_a := λ a, ab.b_to_a (bc.b_to_a a),

  a_b_a := by
  {
    intro a,
    rw bc.a_b_a,
    exact ab.a_b_a _
  },

  b_a_b := by
  {
    intro c,
    rw ab.b_a_b,
    exact bc.b_a_b _
  }
}

-- Task 1-4 : Prove the following statement:
-- Given two functions A → B and B → A, if A → B → A is satisfied and B → A is injective, A ↔ B
def bijection_alt {A B : Type} (ab : A → B) (ba : B → A) 
  (h : ∀ a, ba (ab a) = a) (hba: injective ba) : iso A B :=
{
  a_to_b := ab,
  b_to_a := ba,
  a_b_a := h,
  b_a_b := λ b, hba $ h $ ba b
}

-- Task 2
-- iso relations between nat and various supersets of nat

-- nat_plus_1 : a set having one more element than nat
inductive nat_plus_1 : Type
| null : nat_plus_1
| is_nat (n : ℕ) : nat_plus_1

open nat_plus_1

def nat_iso_nat_plus_1 : iso ℕ nat_plus_1 :=
{
  a_to_b := λ n, nat.rec null (λ m x, is_nat m) n,
    -- send 0 to null and other natural numbers to their predecessor
  b_to_a := λ x, nat_plus_1.rec 0 nat.succ x,
    -- send null to 0 and other nat_plus_1 to the corresponding successor
  a_b_a := λ n, by cases n; dsimp; refl,
  b_a_b := λ x, by cases x; dsimp; refl
}

-- nat_plus_nat : a set having size(nat) more elements than nat.
inductive nat_plus_nat : Type
| left (n : ℕ) : nat_plus_nat
| right (n : ℕ) : nat_plus_nat

open nat_plus_nat
open nat

def nat_to_nat' (n : ℕ) : nat_plus_nat :=
if even n then right $ n/2 else left $ n/2
-- send even numbers to half their right and the odd numbers to half their left

def nat'_to_nat (x : nat_plus_nat) : ℕ :=
nat_plus_nat.cases_on x (λ n, 2*n+1) (λ n, 2*n)
-- send left to one more than double and right to double

lemma two_not_dvd_two_mul_add_one (a : ℕ) : ¬(2 ∣ 2 * a + 1) :=
begin
  convert not_even_bit1 a,
  exact two_mul a,
end

def nat_iso_nat_plus_nat : iso ℕ nat_plus_nat :=
{
  a_to_b := nat_to_nat',
  b_to_a := nat'_to_nat,

  a_b_a := λ n,
  begin
    cases nat.decidable_pred n,
    { have h1 : nat_to_nat' n = _ := if_neg h,
      rw h1,
      unfold nat'_to_nat,
      rw two_mul_odd_div_two (not_even_iff.1 h),
      apply nat.sub_add_cancel,
      show 1 ≤ n,

      cases n,
      { have := even_zero,
        contradiction
      },
      rw add_one_le_iff,
      exact zero_lt_succ n
    },
    have h1 : nat_to_nat' n = _ := if_pos h,
    rw h1,
    unfold nat'_to_nat,
    exact nat.mul_div_cancel' h
  end,

  b_a_b := λ x,
  begin
    cases x;
    unfold nat'_to_nat,
    { have ho := two_not_dvd_two_mul_add_one x,
      have h1 : nat_to_nat' (2*x + 1) = _ := if_neg ho,
      rw h1,
      congr,
      suffices heq : 2 * ((2 * x + 1) / 2) = 2 * x, {linarith},
      rw [two_mul_odd_div_two (not_even_iff.1 ho), nat.add_sub_cancel]
    },
    have he : (2*x).even := ⟨x, rfl⟩,
    have h1 : nat_to_nat' (2*x) = _ := if_pos he,
    rw [h1, nat.mul_div_cancel_left _ (two_pos)]
  end
}