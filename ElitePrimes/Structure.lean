import ElitePrimes.Periodicity

/-!
# Lemma 2.1 (F2), the rest of Lemma 2.2, and Theorem 5.1(b), (d)

* `ord_eq_of_dvd_F`, `ev_ge_of_dvd_F` : Lemma 2.1 (F2).
* `elite_not_dvd_F`, `elite_jacobi_F_p` : Lemma 2.2, `p ∤ F n` and `J(F n | p) = -1`
  for `n ≥ e_p` (the third part, `J(p | F n) = -1`, is `elite_jacobi_p_F`).
* `F_modEq_iff`       : Theorem 5.1(b), exact period `f'_p = ord_{d_p}(2)`.
* `elite_dv_eq_one`   : Theorem 5.1(d), the case `d_p = 1` (then `p ∈ {3, 5}`).
* `elite_structure_d` : Theorem 5.1(d).
-/

namespace ElitePrimes

open Nat Finset

theorem ne_two_of_dvd_F {r n : ℕ} (hrF : r ∣ F n) : r ≠ 2 := by
  rintro rfl
  have h1 := Nat.mod_eq_zero_of_dvd hrF
  have h2 := F_odd n
  omega

/-- Lemma 2.1 (F2): if a prime `r` divides `F n`, then `ord_r(2) = 2^(n+1)`. -/
theorem ord_eq_of_dvd_F {r n : ℕ} (hr : r.Prime) (hrF : r ∣ F n) : ord r = 2 ^ (n + 1) := by
  haveI := Fact.mk hr
  have h0 : ((F n : ℕ) : ZMod r) = 0 := (CharP.cast_eq_zero_iff (ZMod r) r _).mpr hrF
  have hneg : (2 : ZMod r) ^ (2 ^ n) = -1 := by
    rw [F_def] at h0
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hm1 : (-1 : ZMod r) ≠ 1 := by
    intro h
    apply two_ne_zero_zmod (ne_two_of_dvd_F hrF)
    calc (2 : ZMod r) = 1 - (-1) := by ring
      _ = 0 := by rw [h, sub_self]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow
  · rw [hneg]; exact hm1
  · rw [pow_succ, pow_mul, hneg]; norm_num

/-- Lemma 2.1 (F2), consequence: if a prime `r` divides `F n`, then `e_r ≥ n + 1`. -/
theorem ev_ge_of_dvd_F {r n : ℕ} (hr : r.Prime) (hrF : r ∣ F n) : n + 1 ≤ ev r := by
  haveI := Fact.mk hr
  have h := ord_dvd (ne_two_of_dvd_F hrF)
  rw [ord_eq_of_dvd_F hr hrF] at h
  have hne : r - 1 ≠ 0 := by have := hr.two_le; omega
  exact (padicValNat_dvd_iff_le hne).mp h

/-- Lemma 2.2: an elite prime does not divide `F n` for `n ≥ e_p`. -/
theorem elite_not_dvd_F {p : ℕ} (hpe : IsElite p) {n : ℕ} (hn : ev p ≤ n) : ¬ p ∣ F n := by
  intro h
  have := ev_ge_of_dvd_F hpe.1 h
  omega

/-- Lemma 2.2: an elite prime has `J(F n | p) = -1` for every `n ≥ e_p`. -/
theorem elite_jacobi_F_p {p : ℕ} (hpe : IsElite p) {n : ℕ} (hn : ev p ≤ n) :
    jacobiSym (F n) p = -1 := by
  haveI : Fact p.Prime := ⟨hpe.1⟩
  exact elite_jacobi_of_ge_sv hpe (le_trans (sv_le_ev hpe.2.1) hn)

/-- Theorem 5.1(b): for `n ≥ s_p`, `F (n + k) ≡ F n (mod p)` if and only if `f'_p ∣ k`,
where `f'_p = ord_{d_p}(2)`. So `(F n mod p)_{n ≥ s_p}` is purely periodic with exact
period `f'_p`. (For `d_p = 1`, `ZMod 1` is trivial and `f'_p = 1`.) -/
theorem F_modEq_iff {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ} (hn : sv p ≤ n) (k : ℕ) :
    F (n + k) ≡ F n [MOD p] ↔ orderOf (2 : ZMod (dv p)) ∣ k := by
  have hfin : IsOfFinOrder (2 : ZMod p) := orderOf_pos_iff.mp (ord_pos hp2)
  have hcop : Nat.Coprime (2 ^ sv p) (dv p) := Nat.Coprime.pow_left _ (coprime_two_dv hp2)
  -- reduce to `2^(n+k) ≡ 2^n (mod ord_p 2)`
  have h1 : F (n + k) ≡ F n [MOD p] ↔ 2 ^ (n + k) ≡ 2 ^ n [MOD ord p] := by
    rw [← ZMod.natCast_eq_natCast_iff, F_def, F_def]
    push_cast
    rw [add_left_inj]
    exact hfin.pow_eq_pow_iff_modEq
  -- the congruence modulo `2^s_p` always holds
  have h2 : 2 ^ (n + k) ≡ 2 ^ n [MOD 2 ^ sv p] := by
    have a : 2 ^ sv p ∣ 2 ^ (n + k) := Nat.pow_dvd_pow 2 (by omega)
    have b : 2 ^ sv p ∣ 2 ^ n := Nat.pow_dvd_pow 2 hn
    exact (Nat.modEq_zero_iff_dvd.mpr a).trans (Nat.modEq_zero_iff_dvd.mpr b).symm
  have hc : Nat.gcd (dv p) (2 ^ n) = 1 := Nat.Coprime.pow_right n (coprime_two_dv hp2).symm
  rw [h1, ord_eq p, ← Nat.modEq_and_modEq_iff_modEq_mul hcop, and_iff_right h2,
    orderOf_dvd_iff_pow_eq_one, pow_add]
  constructor
  · intro h
    have h' : 2 ^ n * 2 ^ k ≡ 2 ^ n * 1 [MOD dv p] := by rwa [mul_one]
    have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.cancel_left_of_coprime hc h')
    push_cast at h3
    exact h3
  · intro h
    have h3 : ((2 ^ k : ℕ) : ZMod (dv p)) = ((1 : ℕ) : ZMod (dv p)) := by push_cast; exact h
    have h4 := ((ZMod.natCast_eq_natCast_iff _ _ _).mp h3).mul_left (2 ^ n)
    rwa [mul_one] at h4

/-- Theorem 5.1(d), case `d_p = 1`: an elite prime with `d_p = 1` is `3` or `5`. -/
theorem elite_dv_eq_one {p : ℕ} (hpe : IsElite p) (hd : dv p = 1) : p = 3 ∨ p = 5 := by
  haveI : Fact p.Prime := ⟨hpe.1⟩
  have hp2 : p ≠ 2 := hpe.2.1
  have ho : ord p = 2 ^ sv p := by rw [ord_eq p, hd, mul_one]
  by_cases hs : 3 ≤ sv p
  · -- `8 ∣ ord_p 2 ∣ p - 1`, so `J(2 | p) = 1`; but `F (s_p) ≡ 2 (mod p)`
    exfalso
    have h8 : 2 ^ 3 ∣ p - 1 := dvd_trans (ho ▸ Nat.pow_dvd_pow 2 hs) (ord_dvd hp2)
    have hp8 : p % 8 = 1 := by
      have h := Nat.mod_eq_zero_of_dvd h8
      have := hpe.1.two_le
      norm_num at h
      omega
    have hJ2 : jacobiSym 2 p = 1 := by
      rw [jacobiSym.at_two (hpe.1.odd_of_ne_two hp2), ZMod.χ₈_nat_eq_if_mod_eight]
      have hp2' : p % 2 = 1 := by omega
      simp [hp2', hp8]
    have h1 : (2 : ZMod p) ^ (2 ^ sv p) = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
    have hF : jacobiSym (F (sv p)) p = jacobiSym 2 p := by
      apply jacobiSym.mod_left'
      apply (ZMod.intCast_eq_intCast_iff' _ _ _).mp
      push_cast [F_def]
      rw [h1]
      norm_num
    have h := elite_jacobi_of_ge_sv hpe le_rfl
    rw [hF, hJ2] at h
    norm_num at h
  · -- `ord_p 2 ∣ 4`, so `p ∣ 2^4 - 1 = 15`
    have h4 : ord p ∣ 4 := by
      rw [ho]
      exact (Nat.pow_dvd_pow 2 (by omega : sv p ≤ 2) : 2 ^ sv p ∣ 2 ^ 2)
    have h1 : (2 : ZMod p) ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.mp h4
    have h15 : p ∣ 3 * 5 := by
      have h0 : ((3 * 5 : ℕ) : ZMod p) = 0 := by
        have : ((3 * 5 : ℕ) : ZMod p) = (2 : ZMod p) ^ 4 - 1 := by norm_num
        rw [this, h1, sub_self]
      exact (CharP.cast_eq_zero_iff (ZMod p) p _).mp h0
    rcases (Nat.Prime.dvd_mul hpe.1).mp h15 with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpe.1 Nat.prime_three).mp h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hpe.1 Nat.prime_five).mp h)

/-- **Theorem 5.1(d).** If `p` is elite and `p ∉ {3, 5}`, then `d_p > 1` and
`f'_p = ord_{d_p}(2)` is even. -/
theorem elite_structure_d {p : ℕ} (hpe : IsElite p) (h3 : p ≠ 3) (h5 : p ≠ 5) :
    1 < dv p ∧ Even (orderOf (2 : ZMod (dv p))) := by
  haveI : Fact p.Prime := ⟨hpe.1⟩
  have hd : 1 < dv p := by
    have := dv_pos hpe.2.1
    by_contra h
    rcases elite_dv_eq_one hpe (by omega) with h' | h' <;> contradiction
  exact ⟨hd, elite_period_even hpe hd⟩

end ElitePrimes
