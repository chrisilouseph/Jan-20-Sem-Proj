import group_theory.subgroup algebra.pi_instances tactic

/-
Diagonal Subgroup
Problem by mhimmel
(https://www.codewars.com/kata/5eb806b4e7c54e00246f70e1)
-/

-- Definition of the diagonal of a type G, denoted as Δ G:
-- Given G, the set of all elements of G × G where the projections are equal
def Δ (G : Type*) : set (G × G) := { g : G × G | g.fst = g.snd }

-- Given group G and equipping G × G with the product group structure,
-- Δ G is a subgroup of G × G
instance subgroup_Δ (G : Type*) [group G] : is_subgroup (Δ G) :=
{
    one_mem := rfl,

    mul_mem := by
      {rintros ⟨a1, a2⟩ ⟨b1, b2⟩ ha hb,
      change a1 = a2 at ha, change b1 = b2 at hb,
      show a1 * b1 = a2 * b2,
      rw [ha,hb]},

    inv_mem := by
      {rintros ⟨a1, a2⟩ ha,
      change a1 = a2 at ha,
      show a1⁻¹ = a2⁻¹,
      rw ha}
}

-- Given group G, Δ G is a normal subgroup of G × G iff G is abelian
theorem normal_Δ_iff_comm (G : Type*) [group G] :
  normal_subgroup (Δ G) ↔ ∀ g h : G, g * h = h * g :=
⟨by
  {intros hn g h,
  cases hn,
  have h1 : g * h * g⁻¹ = h * h * h⁻¹ := hn_normal (h,h) rfl (g,h),
  have h2 : g * (g * h) * g⁻¹ = h * (g * h) * h⁻¹ := hn_normal (g*h, g*h) rfl (g,h),
  rw [mul_assoc, h1, mul_assoc, mul_right_inv, mul_one] at h2,
  rwa [mul_assoc, mul_assoc, mul_right_inv, mul_one] at h2,},

assume h,
{ normal := by
  {rintros ⟨n1, n2⟩ hn ⟨g1, g2⟩,
  show g1 * n1 * g1⁻¹ = g2 * n2 * g2⁻¹,
  change n1 = n2 at hn,
  rw [hn, h g1 n2, h g2 n2],
  repeat {rw [mul_assoc, mul_right_inv]}},
  ..subgroup_Δ G}⟩

-------------------------------------------

/-
Group Is Not Union Of Two Proper Subgroups
Problem by kckennylau
(https://www.codewars.com/kata/5ea8056e449f540001a2dab2)

If G is a group with subgroups S and T and if G is the union of S and T,
then either S = G or T = G
-/
theorem of_forall_mem_or_mem {G : Type*}
  [group G] (S T : set G) [is_subgroup S] [is_subgroup T]
  (HST : ∀ x, x ∈ S ∨ x ∈ T) : (∀ x, x ∈ S) ∨ (∀ x, x ∈ T) := by
{
    classical, unfreezeI,
    
    by_contra h,
    push_neg at h,
    rcases h with ⟨⟨ns, hns⟩, ⟨nt, hnt⟩⟩,
    -- where ns is an element of G not in S and nt is an element of G not in T
    
    cases HST (ns*nt) with hs ht,
    
        -- Proving that (ns*nt) being in S leads to a contradiction
        
        cases _inst_2, cases _to_is_submonoid,
        replace hnt := or_iff_not_imp_right.1 (HST nt) hnt,
        have hnti := inv_mem hnt,
        have hw := mul_mem hs hnti,
        rw [mul_assoc, mul_inv_self, mul_one] at hw,
        contradiction,
    
    -- Proving that (ns*nt) being in T leads to a contradiction
    
    cases _inst_3, cases _to_is_submonoid,
    replace hns := or_iff_not_imp_left.1 (HST ns) hns,
    have hnsi := inv_mem hns,
    have hw := mul_mem hnsi ht,
    rw [←mul_assoc, inv_mul_self, one_mul] at hw,
    contradiction,
}