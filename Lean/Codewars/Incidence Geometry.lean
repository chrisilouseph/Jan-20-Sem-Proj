import tactic
local attribute [instance] classical.prop_decidable

/-
Incidence Geometry
Problems by donaldsebleung
(https://www.codewars.com/collections/incidence-geometry)

Points and lines are basic undefined types with the incident_with function.
The axioms below are :
I₁ : For each pair of points, there is exactly one line passing through them both.
I₂ : For each line, there exist at least 2 distinct points lying on it.
I₃ : There exist three distinct points that do not all lie on any one line.
-/

class incidence (point line : Type) (incident_with : point → line → Prop) :=
  (I₁ : ∀ P Q, P ≠ Q → ∃! l, incident_with P l ∧ incident_with Q l)
  (I₂ : ∀ l, ∃ P Q, P ≠ Q ∧ incident_with P l ∧ incident_with Q l)
  (I₃ : ∃ P Q R, P ≠ Q ∧ Q ≠ R ∧ P ≠ R ∧
    ∀ l, ¬(incident_with P l ∧ incident_with Q l ∧ incident_with R l))

-- If there is a common point on two distinct lines, then there is exactly
-- one common point on the lines
theorem thm_3p6p1 (point line : Type) (incident_with : point → line → Prop)
  [incidence point line incident_with] (l m : line) (hlm : l ≠ m)
  (hnpar : ∃ P, incident_with P l ∧ incident_with P m) :
  ∃! P, incident_with P l ∧ incident_with P m :=
begin
    cases hnpar with P hp,
    use [P, hp],
    intros Q hq,
    by_contradiction hne,
    rcases @incidence.I₁ point line incident_with _ Q P hne with ⟨n,hqpn,hn⟩,
    apply hlm,
    apply @eq.trans _ _ n,
        exact hn l ⟨hq.1,hp.1⟩,
    symmetry,
    exact hn m ⟨hq.2,hp.2⟩,
end

-- Given a line, there exists a point not lying on it
theorem thm_3p6p2 (point line : Type) (incident_with : point → line → Prop)
  [incidence point line incident_with] (l : line) :
  ∃ P, ¬incident_with P l :=
begin
    rcases (@incidence.I₃ point line incident_with _) with
        ⟨P, Q, R, h1, h2, h3, h⟩,
    push_neg at h,
    rcases (h l) with hw   | hw   | hw,
                      use P, use Q, use R
end

-- Every point lies on atleast two distinct lines
theorem thm_3p6p3 (point line : Type) (incident_with : point → line → Prop)
  [incidence point line incident_with] (P : point) :
  ∃ l m, l ≠ m ∧ incident_with P l ∧ incident_with P m :=
begin
    rcases (@incidence.I₃ point line incident_with _) with
        ⟨Q, R, S, h1, h2, h3, hc⟩,
    rcases @incidence.I₁ point line incident_with _ _ _ h2 with
        ⟨lrs, hlrs, hlrsu⟩,
    
    by_cases hpc : incident_with P lrs,
        have hpq : P ≠ Q,
            intro hpq,
            apply hc lrs,
            rw ←hpq,
            use [hpc,hlrs],
        rcases @incidence.I₁ point line incident_with _ _ _ hpq with
            ⟨lpq, hlpq, hlpqu⟩,
        use [lrs,lpq],
        split,
            intro hw,
            rw ←hw at hlpq,
            apply hc lrs,
            use [hlpq.2,hlrs],
        use [hpc,hlpq.1],
    
    have hpr : P ≠ R,
        intro hw,
        apply hpc,
        rw hw,
        exact hlrs.1,
    have hps : P ≠ S,
        intro hw,
        apply hpc,
        rw hw,
        exact hlrs.2,
    rcases @incidence.I₁ point line incident_with _ _ _ hpr with
        ⟨lpr, hlpr, hlpru⟩,
    rcases @incidence.I₁ point line incident_with _ _ _ hps with
        ⟨lps, hlps, hlpsu⟩,
    use [lpr,lps],
    split,
        intro hw,
        apply hpc,
        suffices hac : lpr = lrs, from hac ▸ (hlpr.1),
        apply hlrsu,
        use hlpr.2,
        rw hw,
        exact hlps.2,
    use [hlpr.1,hlps.1]
end

-- Given a line, there exist two other distinct lines which intersect it
theorem thm_3p6p4 (point line : Type) (incident_with : point → line → Prop)
  [incidence point line incident_with] (l : line) :
  ∃ m n, l ≠ m ∧ m ≠ n ∧ l ≠ n ∧ (∃ P, incident_with P m ∧ incident_with P l) ∧
    ∃ P, incident_with P n ∧ incident_with P l :=
begin
    unfreezeI,
    cases _inst_1,

    have distinct_lines :
      ∀ l m, (∃ P, incident_with P l ∧ ¬ incident_with P m) → l ≠ m,
        rintros m n ⟨X, hxm, hxn⟩ hw,
        rw hw at hxm,
        contradiction,
    
    rcases I₂ l with ⟨A, B, hab, ha, hb⟩,
    rcases I₁ _ _ hab with ⟨lab, hlab, hlabu⟩,
    have hl : l = lab := hlabu _ ⟨ha, hb⟩,
    rw ← hl at *,
    clear hl lab,

    suffices heq : ∃ P, ¬ incident_with P l,
        rcases heq with ⟨X, hx⟩,

        have hax : A ≠ X,
            intro hax,
            rw hax at ha,
            contradiction,
        have hbx : B ≠ X,
            intro hbx,
            rw hbx at hb,
            contradiction,
        
        rcases I₁ _ _ hax with ⟨lax, hlax, hlaxu⟩,
        rcases I₁ _ _ hbx with ⟨lbx, hlbx, hlbxu⟩,

        use [lax,lbx],
        split,
            symmetry,
            apply distinct_lines,
            use [X,hlax.2],
        split,
            apply distinct_lines,
            use [A,hlax.1],
            contrapose! hx,
            have := hlabu _ ⟨hx, hlbx.1⟩,
            rw this at hlbx,
            exact hlbx.right,
        split,
            symmetry,
            apply distinct_lines,
            use [X,hlbx.2],
        use [A, hlax.1, ha, B, hlbx.1, hb],

    rcases I₃ with ⟨P, Q, R, h1, h2, h3, hnl⟩,

    by_cases hc :
      ¬ incident_with P l ∨ ¬ incident_with Q l ∨ ¬ incident_with R l,
        rcases hc with hc | hc | hc,
                use P,
            use Q,
        use R,
    push_neg at hc,
    have := hnl l,
    contradiction
end

-- Given a point, there exists a line not passing through it.
theorem thm_3p6p5 (point line : Type) (incident_with : point → line → Prop)
  [incidence point line incident_with] (P : point) :
  ∃ l, ¬incident_with P l :=
begin
    unfreezeI,
    cases _inst_1,

    rcases I₃ with ⟨S, Q, R, hsq, hqr, hsr, hnl⟩,
    rcases I₁ _ _ hsq with ⟨lsq, hlsq, hlsqu⟩,
    rcases I₁ _ _ hqr with ⟨lqr, hlqr, hlqru⟩,
    rcases I₁ _ _ hsr with ⟨lsr, hlsr, hlsru⟩,

    by_cases hc :
      ¬ incident_with P lsq ∨ ¬ incident_with P lqr ∨ ¬ incident_with P lsr,
        rcases hc with hc | hc | hc,
        use lsq, use lqr, use lsr,
    push_neg at hc,
    
    have hps : P ≠ S,
        intro hw,
        rw hw at hc,
        apply hnl lqr,
        use [hc.2.1,hlqr],

    rcases I₁ _ _ hps with ⟨lps, hlps, hlpsu⟩,

    exfalso,
    apply hnl lps,
    use hlps.2,
    split,
        rw ←hlpsu _ ⟨hc.1, hlsq.1⟩,
        use hlsq.2,
    rw ←hlpsu _ ⟨hc.2.2, hlsr.1⟩,
    use hlsr.2,
end

-- There exist three distinct lines which do not all intersect at the same point.
theorem thm_3p6p6 (point line : Type) (incident_with : point → line → Prop)
  [incidence point line incident_with] :
  ∃ l₁ l₂ l₃, l₁ ≠ l₂ ∧ l₂ ≠ l₃ ∧ l₁ ≠ l₃ ∧ ∀ P, ¬(incident_with P l₁ ∧
    incident_with P l₂ ∧ incident_with P l₃) :=
begin

    unfreezeI,
    cases _inst_1,

    rcases I₃ with ⟨S, Q, R, hsq, hqr, hsr, hnl⟩,
    rcases I₁ _ _ hsq with ⟨lsq, hlsq, hlsqu⟩,
    rcases I₁ _ _ hqr with ⟨lqr, hlqr, hlqru⟩,
    rcases I₁ _ _ hsr with ⟨lsr, hlsr, hlsru⟩,

    use [lsq,lqr,lsr],
    split,
        intro hw,
        replace hw : incident_with S lqr := hw ▸ hlsq.1,
        apply hnl lqr,
        use [hw, hlqr],
    split,
        intro hw,
        replace hw : incident_with Q lsr := hw ▸ hlqr.1,
        apply hnl lsr,
        use [hlsr.1, hw, hlsr.2],
    split,
        intro hw,
        replace hw : incident_with Q lsr := hw ▸ hlsq.2,
        apply hnl lsr,
        use [hlsr.1, hw, hlsr.2],

    intros P hw,

    have hps : P ≠ S,
        intro hps,
        rw hps at hw,
        apply hnl lqr,
        use [hw.2.1,hlqr],
    
    rcases I₁ _ _ hps with ⟨lps, hlps, hlpsu⟩,
    
    exfalso,
    apply hnl lps,
    use hlps.2,
    split,
        rw ←hlpsu _ ⟨hw.1, hlsq.1⟩,
        use hlsq.2,
    rw ←hlpsu _ ⟨hw.2.2, hlsr.1⟩,
    use hlsr.2,
end

-- Given a point, there exist two points such that no line passes through all three.
theorem thm_3p6p7 (point line : Type) (incident_with : point → line → Prop)
  [incidence point line incident_with] (P : point) :
  ∃ Q R, ∀ l, ¬(incident_with P l ∧ incident_with Q l ∧ incident_with R l) :=
begin

    unfreezeI,
    cases _inst_1,

    rcases I₃ with ⟨S, Q, R, hsq, hqr, hsr, hnl⟩,
    rcases I₁ _ _ hsq with ⟨lsq, hlsq, hlsqu⟩,

    by_cases hpl : incident_with P lsq,
        by_cases hps : P = S,

            use [Q,R], rwa hps,
        
        use [S,R],
        rcases I₁ _ _ hps with ⟨lps, hlps, hlpsu⟩,
        intros l hw,
        have h1 := hlpsu _ ⟨hw.1, hw.2.1⟩,
        have h2 := hlpsu _ ⟨hpl, hlsq.1⟩,
        apply hnl lsq,
        use [hlsq.1, hlsq.2],
        rw [h2, ←h1],
        exact hw.2.2,
    
    have not_eq_of_not_incident :
      ∀ X Y l, incident_with Y l → ¬ incident_with X l → X ≠ Y,
        intros X Y l hy hx hxy,
        rw hxy at hx,
        contradiction,
    
    rcases I₁ _ _ (not_eq_of_not_incident _ _ _ hlsq.1 hpl)
        with ⟨lps, hlps, hlpsu⟩,
    rcases I₁ _ _ (not_eq_of_not_incident _ _ _ hlsq.2 hpl)
        with ⟨lpq, hlpq, hlpqu⟩,

    use [S,Q],
    intros l hw,
    have h2 := hlsqu _ hw.2,
    exact hpl (h2 ▸ hw.1),
end

-- Given two distinct points, there exists a point such that
-- no line passes through all three.
theorem thm_3p6p8 (point line : Type) (incident_with : point → line → Prop)
  [incidence point line incident_with] (X Y : point) (hxy : X ≠ Y) :
  ∃ R, ∀ l, ¬(incident_with X l ∧ incident_with Y l ∧ incident_with R l) :=
begin
    unfreezeI,
    cases _inst_1,

    rcases I₃ with ⟨S, Q, R, hsq, hqr, hsr, hnl⟩,
    rcases I₁ _ _ hxy with ⟨lxy, hlxy, hlxyu⟩,

    suffices heq : ∃ R, ¬ incident_with R lxy,

        cases heq with R hr,
        use R,
        intros l hw,
        have h1 := hlxyu _ ⟨hw.1, hw.2.1⟩,
        exact hr (h1 ▸ hw.2.2),
    
    by_cases hc :
      ¬ incident_with S lxy ∨ ¬ incident_with Q lxy ∨ ¬ incident_with R lxy,
        rcases hc with hc | hc | hc,
                use S,
            use Q,
        use R,
    
    push_neg at hc,
    have := hnl lxy,
    contradiction
end