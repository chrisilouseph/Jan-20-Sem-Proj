import tactic logic.function.basic

variables {α : Type*}

/-
relating binary functions
Problems by kbuzzard
(https://www.codewars.com/kata/5ea9b14c9b7bf50001b88e55)
-/

/- We first define the notion of less equal than (with the notation ⊆)
for binary relations as : τ ⊆ σ if and only if for all a, b, we have
τ a b ⇒ σ a b -/
def le' (τ σ : α → α → Prop) := ∀ a b : α, τ a b → σ a b
notation τ ` ⊆ ` σ := le' τ σ

/- We now define the composition of two binary relations τ and σ
(denoted τ ∘ σ) as : for all a b, (τ ∘ σ) a b if and only if there
exists c, such that τ a c ∧ σ c b -/
def comp (τ σ : α → α → Prop) :=
  λ a b : α, ∃ c : α, τ a c ∧ σ c b

notation τ ∘ σ := comp τ σ

/- Prove that ⊆ is both reflexive and transitive -/
theorem le'_refl : @reflexive (α → α → Prop) le' := (λ τ a b, id)

theorem le'_trans : @transitive (α → α → Prop) le' :=
(λ a b c hab hbc x y haxy, hbc _ _ $ hab _ _ haxy)

/- Prove that if two binary relations are reflexive, then so are their
compositions-/
theorem comp_refl {τ σ : α → α → Prop}
  (h₀ : reflexive τ) (h₁ : reflexive σ) :
  reflexive (τ ∘ σ) := (λ x, ⟨x, h₀ x, h₁ x⟩)

/- Prove that composition is associative((a ∘ b) ∘ c)(a ∘ b ∘ c) x -/
theorem comp_assoc : @associative (α → α → Prop) comp := by {

    intros a b c,
    funext x y,
    rw ←iff_eq_eq,

    split;
        intro h,
        rcases h with ⟨p, ⟨s, t, u⟩, r⟩,
        use [s,t,p,u,r],

    rcases h with ⟨p, r, ⟨s, t, u⟩⟩,
    use [s,p,r,t,u],
}

/- Prove that a binary relation τ is transitive if and only if
(τ ∘ τ) ⊆ τ -/
theorem trans_iff_comp_le' {τ : α → α → Prop} :
transitive τ ↔ (τ ∘ τ) ⊆ τ := 
⟨λ h x y ⟨z, hxz, hzy⟩, h hxz hzy,
λ h x y z hxy hyz, h x z ⟨y, hxy, hyz⟩⟩

-------------------------------------------------

/-
Prove that any Inverse of an Involutive Function is itself
Problems by shingtaklam1324
(https://www.codewars.com/kata/5eb8aefefaa14a0001c915e8)
-/

open function

/-
Prove that the left and right inverse of an involutive function
(a self-inverse function) are the function itself
-/

lemma left {α: Type} (f g : α → α)
  (hf : involutive f) (hfg : left_inverse g f) : f = g := by
{
  funext x,
  specialize hfg (f x),
  rw hf at hfg,
  rw hfg
}

lemma right {α: Type} (f g : α → α)
  (hf : involutive f) (hfg : right_inverse g f) : f = g := by
{
  funext x,
  specialize hf (g x),
  rwa hfg at hf
}
