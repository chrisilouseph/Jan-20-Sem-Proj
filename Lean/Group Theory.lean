import algebra

-- Miscellaneous Group Theory Exercises

variables {G : Type} [group G]
variables g h a : G

theorem inv_dis : (g*h)⁻¹ = h⁻¹ * g⁻¹ :=
by {symmetry,
    calc
        h⁻¹ * g⁻¹   = (h⁻¹ * g⁻¹) * 1 : by simp
            ...     = (h⁻¹ * g⁻¹) * ((g*h) * (g*h)⁻¹) : by rw mul_inv_self
            ...     = ((h⁻¹ * (g⁻¹ * g)) * h) * (g*h)⁻¹ : by repeat {rw <-mul_assoc}
            ...     = (h⁻¹ * 1 * h) * (g*h)⁻¹ : by simp
            ...     = (h⁻¹ * h) * (g*h)⁻¹ : by simp
            ...     = 1 * (g*h)⁻¹ : by simp
            ...     = (g*h)⁻¹ : by simp}

theorem mul_right (p : g = h) : g * a = h * a :=
by {rw p}

theorem mul_left (p : g = h) : a * g = a * h :=
by {rw p}

lemma abe1 : (g*h = h*g) <-> ((g*h)⁻¹ = g⁻¹ * h⁻¹) :=
by {split;
    intro P,
        rw P,
        exact inv_dis h g,

        rw <-inv_dis h g at P,
        exact inv_inj P,}

lemma abe2 : (g*h = h*g) <-> ((g*h)*(g*h) = (g*g)*(h*h) ) :=
by {split;
    intro P,
        symmetry,
        have P1 := mul_left (g*h) (h*g) g P,
        have P2 := mul_right _ _ h P1,
        repeat {rw <-mul_assoc, rwa <-mul_assoc at P2},
        
        repeat {rw mul_assoc at P},
        have := group.mul_left_cancel P,
        repeat {rw <-mul_assoc at this},
        have := group.mul_right_cancel this,
        symmetry,
        assumption,}

lemma nilPo_abe (P : ∀ g : G, g * g = 1) : h * a = a * h :=
by {have hnil := P h,
    have hanil := P (h * a),
    have anil := P a,
    apply (abe2 h a).2,
    rw [hnil, anil, hanil],
    simp}