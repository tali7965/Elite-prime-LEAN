import ElitePrimes.Basic

/-!
# Periodicity: Lemma 2.2 and Theorem 5.1(a), (c), (d)

* `ord p = ord_p(2)`, `sv p = s_p = v₂(ord_p 2)`, `dv p = d_p` (odd part of `ord_p 2`).
* `elite_jacobi_of_ge_sv` : Theorem 5.1(c), first half (window starts at `s_p`).
* `elite_extra`           : Theorem 5.1(c), second half (the condition on `2^(2^(s_p - 1))`).
* `elite_period_even`     : Theorem 5.1(d) (period `ord_{d_p}(2)` is even when `d_p > 1`).
* `sv_le_ev`, `sv_lt_ev`  : Theorem 5.1(a).
* `elite_jacobi_p_F`      : Lemma 2.2 (`J(p | F n) = -1` for `n ≥ e_p`).
-/

namespace ElitePrimes

open Nat Finset

/-- `ord p = ord_p(2)`, the multiplicative order of `2` in `ZMod p`. -/
noncomputable def ord (p : ℕ) : ℕ := orderOf (2 : ZMod p)

/-- `sv p = s_p = v₂(ord_p 2)`. -/
noncomputable def sv (p : ℕ) : ℕ := padicValNat 2 (ord p)

/-- `dv p = d_p`, the odd part of `ord_p 2`. -/
noncomputable def dv (p : ℕ) : ℕ := ord p / 2 ^ sv p

theorem ord_eq (p : ℕ) : ord p = 2 ^ sv p * dv p :=
  (Nat.mul_div_cancel' pow_padicValNat_dvd).symm

section prime

variable {p : ℕ} [hp : Fact p.Prime]

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (ZMod p) p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')

theorem ord_dvd (hp2 : p ≠ 2) : ord p ∣ p - 1 :=
  ZMod.orderOf_dvd_card_sub_one (two_ne_zero_zmod hp2)

theorem ord_pos (hp2 : p ≠ 2) : 0 < ord p := by
  have h1 : 0 < p - 1 := by have := hp.out.two_le; omega
  exact Nat.pos_of_dvd_of_pos (ord_dvd hp2) h1

theorem dv_odd (hp2 : p ≠ 2) : ¬ 2 ∣ dv p := by
  intro h
  have hne : ord p ≠ 0 := (ord_pos hp2).ne'
  apply pow_succ_padicValNat_not_dvd (p := 2) hne
  rw [pow_succ]
  conv_rhs => rw [ord_eq p]
  exact Nat.mul_dvd_mul_left _ h

theorem dv_pos (hp2 : p ≠ 2) : 0 < dv p := by
  rcases Nat.eq_zero_or_pos (dv p) with h | h
  · have := ord_pos hp2
    rw [ord_eq p, h, mul_zero] at this
    exact absurd this (lt_irrefl 0)
  · exact h

theorem coprime_two_dv (hp2 : p ≠ 2) : Nat.Coprime 2 (dv p) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (dv_odd hp2)

/-- Key periodicity: for `n ≥ s_p`, `2^(2^(n + φ(d_p) j)) = 2^(2^n)` in `ZMod p`. -/
theorem two_pow_two_pow_periodic (hp2 : p ≠ 2) {n : ℕ} (hn : sv p ≤ n) (j : ℕ) :
    (2 : ZMod p) ^ (2 ^ (n + (dv p).totient * j)) = (2 : ZMod p) ^ (2 ^ n) := by
  set t := (dv p).totient * j with ht
  have heuler : 2 ^ t ≡ 1 [MOD dv p] := by
    have h := (Nat.ModEq.pow_totient (coprime_two_dv hp2)).pow j
    rw [one_pow, ← pow_mul] at h
    exact h
  have hd : dv p ∣ 2 ^ t - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp heuler.symm
  have hs : 2 ^ sv p ∣ 2 ^ n := Nat.pow_dvd_pow 2 hn
  have hord : ord p ∣ 2 ^ (n + t) - 2 ^ n := by
    have h1 : 2 ^ (n + t) - 2 ^ n = 2 ^ n * (2 ^ t - 1) := by
      rw [pow_add, Nat.mul_sub_one]
    rw [h1, ord_eq p]
    exact Nat.mul_dvd_mul hs hd
  have hle : 2 ^ n ≤ 2 ^ (n + t) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right n t)
  obtain ⟨k, hk⟩ := hord
  have hexp : 2 ^ (n + t) = 2 ^ n + ord p * k := by
    rw [← hk]; exact (Nat.add_sub_cancel' hle).symm
  rw [hexp, pow_add, pow_mul,
    show (2 : ZMod p) ^ ord p = 1 from pow_orderOf_eq_one _, one_pow, mul_one]

theorem jacobi_F_periodic (hp2 : p ≠ 2) {n : ℕ} (hn : sv p ≤ n) (j : ℕ) :
    jacobiSym (F (n + (dv p).totient * j)) p = jacobiSym (F n) p := by
  apply jacobiSym.mod_left'
  have h : ((F (n + (dv p).totient * j) : ℕ) : ZMod p) = ((F n : ℕ) : ZMod p) := by
    simp only [F_def]
    push_cast
    rw [two_pow_two_pow_periodic hp2 hn j]
  have h2 : F (n + (dv p).totient * j) % p = F n % p :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
  exact_mod_cast h2

/-- Theorem 5.1(a), first half: `s_p ≤ e_p`. -/
theorem sv_le_ev (hp2 : p ≠ 2) : sv p ≤ ev p := by
  have h1 : 2 ^ sv p ∣ p - 1 := dvd_trans pow_padicValNat_dvd (ord_dvd hp2)
  have hne : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  exact (padicValNat_dvd_iff_le hne).mp h1

/-- Theorem 5.1(a), second half: if `e_p ≥ 3` then `s_p ≤ e_p - 1`. -/
theorem sv_lt_ev (hp2 : p ≠ 2) (h3 : 3 ≤ ev p) : sv p + 1 ≤ ev p := by
  have hne : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  have h8 : 2 ^ 3 ∣ p - 1 := (padicValNat_dvd_iff_le hne).mpr h3
  norm_num at h8
  have hp8 : p % 8 = 1 := by
    have h := Nat.mod_eq_zero_of_dvd h8
    have := hp.out.two_le
    omega
  have hsq : IsSquare (2 : ZMod p) := (ZMod.exists_sq_eq_two_iff hp2).mpr (Or.inl hp8)
  have heul : (2 : ZMod p) ^ (p / 2) = 1 :=
    (ZMod.euler_criterion p (two_ne_zero_zmod hp2)).mp hsq
  have hord : ord p ∣ p / 2 := orderOf_dvd_of_pow_eq_one heul
  have h2 : 2 ^ sv p * 2 ∣ p - 1 := by
    have h4 : 2 ^ sv p ∣ p / 2 := dvd_trans pow_padicValNat_dvd hord
    have hp1 : p - 1 = p / 2 * 2 := by omega
    rw [hp1]
    exact Nat.mul_dvd_mul_right h4 2
  rw [← pow_succ] at h2
  exact (padicValNat_dvd_iff_le hne).mp h2

end prime

/-- Theorem 5.1(c), first half: an elite prime has `J(F n | p) = -1` for every `n ≥ s_p`. -/
theorem elite_jacobi_of_ge_sv {p : ℕ} (hpe : IsElite p) {n : ℕ} (hn : sv p ≤ n) :
    jacobiSym (F n) p = -1 := by
  haveI : Fact p.Prime := ⟨hpe.1⟩
  have hp2 : p ≠ 2 := hpe.2.1
  obtain ⟨n₀, hn₀⟩ := hpe.2.2
  have hφ : 0 < (dv p).totient := Nat.totient_pos.mpr (dv_pos hp2)
  rw [← jacobi_F_periodic hp2 hn n₀]
  apply hn₀
  have h1 : n₀ ≤ (dv p).totient * n₀ := Nat.le_mul_of_pos_left n₀ hφ
  omega

/-- Theorem 5.1(c), second half: if `s_p ≥ 1` then `J(1 - 2^(2^(s_p - 1)) | p) = -1`. -/
theorem elite_extra {p : ℕ} (hpe : IsElite p) (hs : 1 ≤ sv p) :
    jacobiSym (1 - 2 ^ (2 ^ (sv p - 1))) p = -1 := by
  haveI : Fact p.Prime := ⟨hpe.1⟩
  have hp2 : p ≠ 2 := hpe.2.1
  have ho : ord p = 2 ^ sv p * dv p := ord_eq p
  have hdpos := dv_pos hp2
  have hφ : 0 < (dv p).totient := Nat.totient_pos.mpr hdpos
  -- dv p ∣ 2^φ(d) - 1 with odd cofactor q = 2r + 1
  obtain ⟨q, hq⟩ : dv p ∣ 2 ^ (dv p).totient - 1 :=
    (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp (Nat.ModEq.pow_totient (coprime_two_dv hp2)).symm
  have hodd : (2 ^ (dv p).totient - 1) % 2 = 1 := by
    have h1 : 2 ∣ 2 ^ (dv p).totient := dvd_pow_self 2 hφ.ne'
    have h2 := Nat.mod_eq_zero_of_dvd h1
    have h3 : 1 ≤ 2 ^ (dv p).totient := Nat.one_le_two_pow
    omega
  have hqodd : Odd q := by
    have h1 : Odd (dv p * q) := by rw [← hq]; exact Nat.odd_iff.mpr hodd
    exact (Nat.odd_mul.mp h1).2
  obtain ⟨r, hr⟩ := hqodd
  -- h = 2^(s-1) d, ord p = 2h, and 2^h = -1
  set h := 2 ^ (sv p - 1) * dv p with hh
  have hs2 : 2 ^ sv p = 2 * 2 ^ (sv p - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hoh : ord p = 2 * h := by rw [ho, hs2, hh, mul_assoc]
  have hhpos : 0 < h := Nat.mul_pos (by positivity) hdpos
  have hneg : (2 : ZMod p) ^ h = -1 := by
    have hsq : (2 : ZMod p) ^ h * (2 : ZMod p) ^ h = 1 := by
      rw [← pow_add, ← two_mul, ← hoh]
      exact pow_orderOf_eq_one _
    have hne1 : (2 : ZMod p) ^ h ≠ 1 := by
      apply pow_ne_one_of_lt_orderOf hhpos.ne'
      show h < ord p
      rw [hoh]; omega
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · exact absurd h1 hne1
    · exact h1
  -- m = s - 1 + φ(d): 2^m = 2^(s-1) + h + ord p * r
  set m := sv p - 1 + (dv p).totient with hm
  have hmexp : 2 ^ m = 2 ^ (sv p - 1) + h + ord p * r := by
    have h1 : 2 ^ (dv p).totient = dv p * q + 1 := by
      have : 1 ≤ 2 ^ (dv p).totient := Nat.one_le_two_pow
      omega
    rw [hm, pow_add, h1, hr, hoh, hh]
    ring
  have hval : (2 : ZMod p) ^ (2 ^ m) = -(2 : ZMod p) ^ (2 ^ (sv p - 1)) := by
    rw [hmexp, pow_add, pow_add, pow_mul (2 : ZMod p) (ord p) r, hneg,
      show (2 : ZMod p) ^ ord p = 1 from pow_orderOf_eq_one _, one_pow]
    ring
  -- m ≥ s_p, so J(F m | p) = -1, and F m ≡ 1 - 2^(2^(s-1)) (mod p)
  have hm_ge : sv p ≤ m := by rw [hm]; omega
  have hJ : jacobiSym (F m) p = -1 := elite_jacobi_of_ge_sv hpe hm_ge
  rw [← hJ]
  apply jacobiSym.mod_left'
  apply (ZMod.intCast_eq_intCast_iff' _ _ _).mp
  push_cast [F_def]
  rw [hval]
  ring

/-- Telescoping: `(y - 1) ∏_{j<N} (1 + y^(2^j)) = y^(2^N) - 1`. -/
theorem telescope {R : Type*} [CommRing R] (y : R) (N : ℕ) :
    (y - 1) * ∏ j ∈ range N, (1 + y ^ (2 ^ j)) = y ^ (2 ^ N) - 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih, pow_succ, pow_mul]
    ring

theorem jacobiSym_prod_left (b : ℕ) (f : ℕ → ℤ) (N : ℕ) :
    jacobiSym (∏ j ∈ range N, f j) b = ∏ j ∈ range N, jacobiSym (f j) b := by
  induction N with
  | zero => simp [jacobiSym.one_left]
  | succ N ih => rw [Finset.prod_range_succ, Finset.prod_range_succ, jacobiSym.mul_left, ih]

/-- Theorem 5.1(d), case `d_p > 1`: if `p` is elite and `d_p > 1`, then `ord_{d_p}(2)` is even. -/
theorem elite_period_even {p : ℕ} (hpe : IsElite p) (hd : 1 < dv p) :
    Even (orderOf (2 : ZMod (dv p))) := by
  haveI : Fact p.Prime := ⟨hpe.1⟩
  have hp2 : p ≠ 2 := hpe.2.1
  have ho : ord p = 2 ^ sv p * dv p := ord_eq p
  set f := orderOf (2 : ZMod (dv p)) with hfdef
  -- dv p ∣ 2^f - 1
  have hfd : dv p ∣ 2 ^ f - 1 := by
    have h1 : (2 : ZMod (dv p)) ^ f = 1 := pow_orderOf_eq_one _
    have h2 : ((2 ^ f : ℕ) : ZMod (dv p)) = ((1 : ℕ) : ZMod (dv p)) := by
      push_cast; exact h1
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp h2.symm
  -- y = 2^(2^s) ≠ 1 and y^(2^f) = y
  set y : ZMod p := (2 : ZMod p) ^ (2 ^ sv p) with hy
  have hy1 : y ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf (by positivity)
    show 2 ^ sv p < ord p
    rw [ho]
    exact lt_mul_of_one_lt_right (by positivity) hd
  have hyf : y ^ (2 ^ f) = y := by
    rw [hy, ← pow_mul]
    have hdiv : ord p ∣ 2 ^ sv p * 2 ^ f - 2 ^ sv p := by
      rw [ho, ← Nat.mul_sub_one]
      exact Nat.mul_dvd_mul_left _ hfd
    have hle : 2 ^ sv p ≤ 2 ^ sv p * 2 ^ f := Nat.le_mul_of_pos_right _ (by positivity)
    obtain ⟨k, hk⟩ := hdiv
    have hexp : 2 ^ sv p * 2 ^ f = 2 ^ sv p + ord p * k := by
      rw [← hk]; exact (Nat.add_sub_cancel' hle).symm
    rw [hexp, pow_add, pow_mul,
      show (2 : ZMod p) ^ ord p = 1 from pow_orderOf_eq_one _, one_pow, mul_one]
  -- telescoping product equals 1
  have hprod : ∏ j ∈ range f, (1 + y ^ (2 ^ j)) = 1 := by
    have ht := telescope y f
    rw [hyf] at ht
    have hne : y - 1 ≠ 0 := sub_ne_zero.mpr hy1
    exact mul_left_cancel₀ hne (by rw [ht, mul_one])
  have hfac : ∀ j, (1 + y ^ (2 ^ j) : ZMod p) = ((F (sv p + j) : ℕ) : ZMod p) := by
    intro j
    rw [hy, ← pow_mul, ← pow_add, F_def]
    push_cast
    ring
  -- so ∏ J(F (s+j) | p) = J(1 | p) = 1
  have hJ : ∏ j ∈ range f, jacobiSym (F (sv p + j)) p = 1 := by
    have hpl := jacobiSym_prod_left p (fun j => ((F (sv p + j) : ℕ) : ℤ)) f
    try simp only at hpl
    rw [← hpl]
    have hmod : (∏ j ∈ range f, ((F (sv p + j) : ℕ) : ℤ)) % (p : ℤ) = (1 : ℤ) % (p : ℤ) := by
      apply (ZMod.intCast_eq_intCast_iff' _ _ _).mp
      push_cast
      rw [← hprod]
      apply Finset.prod_congr rfl
      intro j _
      rw [hfac j]
    rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]
  -- but each factor is -1 (Theorem 5.1(c)), so (-1)^f = 1
  have hneg : ∏ j ∈ range f, jacobiSym (F (sv p + j)) p = (-1) ^ f := by
    rw [Finset.prod_congr rfl (fun j _ => elite_jacobi_of_ge_sv hpe (Nat.le_add_right (sv p) j)),
      Finset.prod_const, Finset.card_range]
  rw [hneg] at hJ
  exact (neg_one_pow_eq_one_iff_even (by decide)).mp hJ

theorem one_le_ev {p : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2) : 1 ≤ ev p := by
  have hodd := hpp.odd_of_ne_two hp2
  have h2 : 2 ∣ p - 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  have hpos : 0 < p - 1 := by have := hpp.two_le; omega
  exact one_le_padicValNat_of_dvd hpos.ne' h2

/-- Lemma 2.2: an elite prime satisfies `J(p | F n) = -1` for every `n ≥ e_p`. -/
theorem elite_jacobi_p_F {p : ℕ} (hpe : IsElite p) {n : ℕ} (hn : ev p ≤ n) :
    jacobiSym p (F n) = -1 := by
  haveI : Fact p.Prime := ⟨hpe.1⟩
  have hp2 : p ≠ 2 := hpe.2.1
  have hn1 : 1 ≤ n := le_trans (one_le_ev hpe.1 hp2) hn
  have h1 : jacobiSym (F n) p = -1 := elite_jacobi_of_ge_sv hpe (le_trans (sv_le_ev hp2) hn)
  rw [← h1]
  exact (jacobiSym.quadratic_reciprocity_one_mod_four (F_mod_four hn1)
    (hpe.1.odd_of_ne_two hp2)).symm

/-- `p ≡ 1 + 2^(e_p) (mod 2^(e_p + 1))` for an odd prime `p`. -/
theorem mod_pow_ev {p : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2) :
    p % 2 ^ (ev p + 1) = 1 + 2 ^ ev p := by
  set e := ev p with he
  have hne : p - 1 ≠ 0 := by have := hpp.two_le; omega
  obtain ⟨k, hk⟩ : 2 ^ e ∣ p - 1 := pow_padicValNat_dvd
  have hk_odd : k % 2 = 1 := by
    by_contra hcon
    have hk2 : 2 ∣ k := by omega
    apply pow_succ_padicValNat_not_dvd (p := 2) hne
    show 2 ^ (e + 1) ∣ p - 1
    rw [hk, pow_succ]
    exact Nat.mul_dvd_mul_left _ hk2
  have hp : p = 2 ^ e * k + 1 := by have := hpp.two_le; omega
  obtain ⟨r, hr⟩ : ∃ r, k = 2 * r + 1 := ⟨k / 2, by omega⟩
  have he1 : 1 ≤ e := one_le_ev hpp hp2
  have hlt : 1 + 2 ^ e < 2 ^ (e + 1) := by
    have h1 : 1 < 2 ^ e := Nat.one_lt_two_pow (by omega)
    rw [pow_succ]; omega
  rw [hp, hr]
  have hre : 2 ^ e * (2 * r + 1) + 1 = (1 + 2 ^ e) + 2 ^ (e + 1) * r := by
    rw [pow_succ]; ring
  rw [hre, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- If `T ≤ e_p` then `p ≡ 1 (mod 2^T)`. -/
theorem mod_pow_of_le_ev {p : ℕ} (hpp : p.Prime) {T : ℕ} (hT : T ≤ ev p) :
    p % 2 ^ T = 1 % 2 ^ T := by
  have h : 2 ^ T ∣ p - 1 := dvd_trans (Nat.pow_dvd_pow 2 hT) pow_padicValNat_dvd
  have := hpp.two_le
  exact ((Nat.modEq_iff_dvd' (by omega : 1 ≤ p)).mpr h).symm

end ElitePrimes
