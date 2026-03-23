import Mathlib

lemma one_le_fac (n : ℕ) : 1 ≤ n.factorial := by
  induction' n with n hn
  · simp
  · unfold Nat.factorial
    nlinarith

lemma two_le_fac_add_one (n : ℕ) : 2 ≤ n.factorial + 1 := by
  linarith [one_le_fac n]

lemma step_2 (p n : ℕ) (hn : 0 < n) (h1 : p.Prime) (h2 : p ∣ n.factorial + 1) : ¬ (p ∣ n) := by
  by_contra h
  have h3 : p ∣ n.factorial := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_one.mpr hn
    rw [hm, Nat.factorial, Nat.succ_eq_add_one, ← hm, dvd_mul]
    use p, 1
    simp only [isUnit_iff_eq_one, IsUnit.dvd, mul_one, and_self, and_true]
    exact h
  apply Nat.Prime.not_dvd_one h1
  zify at *
  have hrw : (1 : ℤ) = n.factorial + 1 - n.factorial := by ring
  rw [hrw]
  exact dvd_sub h2 h3
