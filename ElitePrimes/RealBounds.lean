import ElitePrimes.TheoremA

/-!
# Proposition 3.1 and inequality (2) for real `x`

The elite primes `p ≤ x` are those in `eliteSet ⌊x⌋₊`. The bounds of `TheoremA.lean` are
stated at integers `N`; they pass to real `x` because `log t / t` is decreasing for `t ≥ e`.

* `block_bound_real`     : inequality (4) for real `x`.
* `big_block_bound_real` : inequality (5) for real `x`.
* `theoremA_real`        : inequality (2) for real `x`.
* `theoremA_asymp`       : Theorem 1.1, `E(x) ≤ (16 + o(1)) x log log x / (log x)^2`.
-/

namespace ElitePrimes

open Nat Finset

/-- From `N = ⌊x⌋₊` to `x`: if `c log N ≤ K N` and `x ≥ 3`, then `c log x ≤ K x`. -/
theorem real_of_floor {x c K : ℝ} (hc : 0 ≤ c) (h3 : 3 ≤ x)
    (h : c * Real.log ⌊x⌋₊ ≤ K * ⌊x⌋₊) : c * Real.log x ≤ K * x := by
  set N := ⌊x⌋₊ with hNdef
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hN3 : (3 : ℝ) ≤ N := by
    have : 3 ≤ N := Nat.le_floor (by exact_mod_cast h3)
    exact_mod_cast this
  have he : Real.exp 1 ≤ (N : ℝ) :=
    le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hN3
  have hanti := Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he)
    (Set.mem_Ici.mpr (le_trans he hNx)) hNx
  have hNpos : (0 : ℝ) < N := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  simp only at hanti
  rw [div_le_div_iff₀ hxpos hNpos] at hanti
  -- hanti : log x * N ≤ log N * x
  have key : c * Real.log x * (N * Real.log N) ≤ K * x * (N * Real.log N) := by
    calc c * Real.log x * (N * Real.log N) = c * (Real.log x * N) * Real.log N := by ring
      _ ≤ c * (Real.log N * x) * Real.log N := by gcongr
      _ = (c * Real.log N) * (x * Real.log N) := by ring
      _ ≤ (K * N) * (x * Real.log N) := by gcongr
      _ = K * x * (N * Real.log N) := by ring
  exact le_of_mul_le_mul_right key (by positivity)

theorem three_le_of_hyp {x : ℝ} {T : ℕ} (hT : 1 ≤ T)
    (hx : ((2 ^ T * 2 ^ (2 ^ T)) ^ 2 : ℝ) ≤ x) : 3 ≤ x := by
  have h1 : (2 : ℝ) ≤ 2 ^ T := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ T := pow_le_pow_right₀ (by norm_num) hT
  have h2 : (1 : ℝ) ≤ 2 ^ (2 ^ T) := one_le_pow₀ (by norm_num)
  have h3 : (2 : ℝ) ≤ 2 ^ T * 2 ^ (2 ^ T) := by nlinarith
  have h4 : (4 : ℝ) ≤ (2 ^ T * 2 ^ (2 ^ T)) ^ 2 := by nlinarith
  linarith

theorem nat_hyp {x : ℝ} {T : ℕ} (hx : ((2 ^ T * 2 ^ (2 ^ T)) ^ 2 : ℝ) ≤ x) :
    (2 ^ T * 2 ^ (2 ^ T)) ^ 2 ≤ ⌊x⌋₊ :=
  Nat.le_floor (by push_cast; exact hx)

/-- Inequality (4) for real `x`: if `1 ≤ e < T` and `(2^T 2^(2^T))^2 ≤ x`, then
`#{p ≤ x elite : e_p = e} · 2^T log x ≤ 4x`. -/
theorem block_bound_real (hBT : BrunTitchmarsh) {x : ℝ} {T e : ℕ} (he1 : 1 ≤ e) (heT : e < T)
    (hx : ((2 ^ T * 2 ^ (2 ^ T)) ^ 2 : ℝ) ≤ x) :
    (((eliteSet ⌊x⌋₊).filter (fun p => ev p = e)).card : ℝ) * (2 ^ T * Real.log x) ≤ 4 * x := by
  have h := block_bound hBT he1 heT (nat_hyp hx)
  have h' := real_of_floor (c := ((eliteSet ⌊x⌋₊).filter (fun p => ev p = e)).card * 2 ^ T)
    (K := 4) (by positivity) (three_le_of_hyp (by omega) hx)
    (by linarith [h])
  linarith [h']

/-- Inequality (5) for real `x`: if `T ≥ 1` and `(2^T 2^(2^T))^2 ≤ x`, then
`#{p ≤ x elite : e_p ≥ T} · 2^T log x ≤ 8x`. -/
theorem big_block_bound_real (hBT : BrunTitchmarsh) {x : ℝ} {T : ℕ} (hT : 1 ≤ T)
    (hx : ((2 ^ T * 2 ^ (2 ^ T)) ^ 2 : ℝ) ≤ x) :
    (((eliteSet ⌊x⌋₊).filter (fun p => T ≤ ev p)).card : ℝ) * (2 ^ T * Real.log x) ≤ 8 * x := by
  have h := big_block_bound hBT hT (nat_hyp hx)
  have h' := real_of_floor (c := ((eliteSet ⌊x⌋₊).filter (fun p => T ≤ ev p)).card * 2 ^ T)
    (K := 8) (by positivity) (three_le_of_hyp hT hx) (by linarith [h])
  linarith [h']

/-- **Inequality (2)** for real `x`. Assuming Brun–Titchmarsh, for `T ≥ 1` and
`(2^T 2^(2^T))^2 ≤ x`: `E(x) · 2^T log x ≤ 4 (T + 1) x`, where `E(x) = E ⌊x⌋₊`. -/
theorem theoremA_real (hBT : BrunTitchmarsh) {x : ℝ} {T : ℕ} (hT : 1 ≤ T)
    (hx : ((2 ^ T * 2 ^ (2 ^ T)) ^ 2 : ℝ) ≤ x) :
    (E ⌊x⌋₊ : ℝ) * (2 ^ T * Real.log x) ≤ 4 * (T + 1) * x := by
  have h := theoremA hBT ⌊x⌋₊ T hT (nat_hyp hx)
  have h' := real_of_floor (c := (E ⌊x⌋₊ : ℝ) * 2 ^ T) (K := 4 * (T + 1)) (by positivity)
    (three_le_of_hyp hT hx) (by linarith [h])
  linarith [h']

theorem log_hyp (T : ℕ) :
    Real.log (((2 : ℝ) ^ T * 2 ^ (2 ^ T)) ^ 2) = (2 * T + 2 ^ (T + 1)) * Real.log 2 := by
  rw [show ((2 : ℝ) ^ T * 2 ^ (2 ^ T)) ^ 2 = 2 ^ (2 * T + 2 ^ (T + 1)) by
    rw [← pow_add, ← pow_mul]; congr 1; ring]
  rw [Real.log_pow]
  push_cast
  ring

/-- **Theorem 1.1** (asymptotic form). Assuming Brun–Titchmarsh, for every `ε > 0` and all
large `x`, `E(x) ≤ (16 + ε) x log log x / (log x)^2`. -/
theorem theoremA_asymp (hBT : BrunTitchmarsh) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀,
      (E ⌊x⌋₊ : ℝ) ≤ (16 + ε) * x * Real.log (Real.log x) / Real.log x ^ 2 := by
  classical
  set δ := ε / 16 with hδ
  have hδ0 : 0 < δ := by positivity
  set A : ℝ := (12 * (1 + δ) / δ) ^ 2 with hA
  set K : ℝ := max (2 / δ) A + 5 with hK
  refine ⟨Real.exp (Real.exp K), fun x hx => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  set L := Real.log x with hL
  have hLK : Real.exp K ≤ L := (Real.le_log_iff_exp_le hxpos).mpr hx
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hLK
  set ℓ := Real.log L with hℓ
  have hℓK : K ≤ ℓ := (Real.le_log_iff_exp_le hL0).mpr hLK
  have hKA : A + 5 ≤ K := by rw [hK]; linarith [le_max_right (2 / δ) A]
  have hKd : 2 / δ ≤ K := by rw [hK]; linarith [le_max_left (2 / δ) A]
  have hKL : K + 1 ≤ L := le_trans (Real.add_one_le_exp K) hLK
  have hLA : A ≤ L := by linarith
  have hℓδ : 2 ≤ δ * ℓ := by
    have : 2 / δ ≤ ℓ := by linarith
    rwa [div_le_iff₀ hδ0, mul_comm] at this
  have hℓ0 : 0 < ℓ := by linarith [show (0 : ℝ) ≤ A by positivity]
  -- `√L` bounds
  set r := Real.sqrt L with hrdef
  have hr : 0 < r := Real.sqrt_pos.mpr hL0
  have hrr : r * r = L := Real.mul_self_sqrt hL0.le
  have hr1 : 12 * (1 + δ) / δ ≤ r := by
    have := Real.sqrt_le_sqrt hLA
    rwa [hA, Real.sqrt_sq (by positivity)] at this
  have hr12 : 12 * (1 + δ) ≤ δ * r := by
    rw [div_le_iff₀ hδ0] at hr1; linarith
  have hr1' : 1 ≤ r := by
    have : (12 : ℝ) ≤ 12 * (1 + δ) / δ := by rw [le_div_iff₀ hδ0]; linarith
    linarith
  have hℓr : ℓ ≤ 2 * r := by
    have h1 : Real.log r = ℓ / 2 := by rw [hrdef, Real.log_sqrt hL0.le]
    have h2 := Real.log_le_sub_one_of_pos hr
    linarith
  -- `log 2` and `x ≥ 64`
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hl2 : 0 < Real.log 2 := by linarith
  have hx64 : (64 : ℝ) ≤ x := by
    have h1 : Real.log 64 < L := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      push_cast
      linarith [show (0 : ℝ) ≤ A by positivity]
    exact ((Real.log_lt_log_iff (by norm_num) hxpos).mp h1).le
  -- `T` maximal with `(2^T 2^(2^T))^2 ≤ x`
  let P : ℕ → Prop := fun T => ((2 ^ T * 2 ^ (2 ^ T)) ^ 2 : ℝ) ≤ x
  have hP1 : P 1 := by show ((2 ^ 1 * 2 ^ (2 ^ 1)) ^ 2 : ℝ) ≤ x; norm_num; linarith
  have h1n : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
  set T := Nat.findGreatest P ⌊x⌋₊ with hTdef
  have hPT : P T := Nat.findGreatest_spec h1n hP1
  have hT1 : 1 ≤ T := Nat.le_findGreatest h1n hP1
  have hTn : T + 1 ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    have h1 : ((T + 1 : ℕ) : ℝ) ≤ 2 ^ T := by
      exact_mod_cast Nat.succ_le_of_lt Nat.lt_two_pow_self
    have h2 : (1 : ℝ) ≤ 2 ^ (2 ^ T) := one_le_pow₀ (by norm_num)
    have h3 : (2 : ℝ) ^ T ≤ 2 ^ T * 2 ^ (2 ^ T) := le_mul_of_one_le_right (by positivity) h2
    have h4 : (1 : ℝ) ≤ 2 ^ T * 2 ^ (2 ^ T) := le_trans (one_le_pow₀ (by norm_num)) h3
    have h5 : (2 : ℝ) ^ T * 2 ^ (2 ^ T) ≤ (2 ^ T * 2 ^ (2 ^ T)) ^ 2 := by nlinarith
    have h6 : ((2 ^ T * 2 ^ (2 ^ T)) ^ 2 : ℝ) ≤ x := hPT
    linarith
  have hnotP : ¬ P (T + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self T) hTn
  have hup : (2 * T + 2 ^ (T + 1)) * Real.log 2 ≤ L := by
    rw [← log_hyp]; exact Real.log_le_log (by positivity) hPT
  have hlow : L < (2 * (T + 1) + 4 * 2 ^ T) * Real.log 2 := by
    have h := Real.log_lt_log hxpos (lt_of_not_ge hnotP)
    rw [log_hyp] at h
    push_cast at h
    calc L < (2 * (T + 1) + 2 ^ (T + 1 + 1)) * Real.log 2 := h
      _ = (2 * (T + 1) + 4 * 2 ^ T) * Real.log 2 := by ring
  -- `(T + 1) log 2 ≤ log log x + 1`
  have h2T1 : (2 : ℝ) ^ (T + 1) ≤ 2 * L := by
    have h0 : (0 : ℝ) ≤ 2 * T * Real.log 2 := by positivity
    have h1 : (2 : ℝ) ^ (T + 1) * (1 / 2) ≤ 2 ^ (T + 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : (2 * T + 2 ^ (T + 1)) * Real.log 2 = 2 * T * Real.log 2 + 2 ^ (T + 1) * Real.log 2 := by
      ring
    linarith
  have hTℓ : (T + 1) * Real.log 2 ≤ ℓ + 1 := by
    have h := Real.log_le_log (by positivity) h2T1
    rw [Real.log_pow, Real.log_mul (by norm_num) hL0.ne'] at h
    push_cast at h
    linarith
  -- the bound `E · (L - 2(ℓ+1)) · L ≤ 16 (ℓ+1) x`
  have hE := theoremA_real hBT hT1 hPT
  set Ex : ℝ := (E ⌊x⌋₊ : ℝ) with hEx
  have hE0 : 0 ≤ Ex := Nat.cast_nonneg _
  have hkey : 4 * (1 + δ) * (ℓ + 1) ≤ δ * L := by
    have : ℓ + 1 ≤ 3 * r := by linarith
    calc 4 * (1 + δ) * (ℓ + 1) ≤ 4 * (1 + δ) * (3 * r) := by gcongr
      _ = 12 * (1 + δ) * r := by ring
      _ ≤ δ * r * r := by gcongr
      _ = δ * L := by rw [mul_assoc, hrr]
  set D := L - 2 * (ℓ + 1) with hD
  have hL4 : 4 * (ℓ + 1) < L := by
    by_contra hc
    replace hc := not_lt.mp hc
    have h1 : δ * L ≤ δ * (4 * (ℓ + 1)) := mul_le_mul_of_nonneg_left hc hδ0.le
    have h2 : 4 * (1 + δ) * (ℓ + 1) = 4 * (ℓ + 1) + δ * (4 * (ℓ + 1)) := by ring
    linarith
  have hDpos : 0 < D := by rw [hD]; linarith
  have hDle : D ≤ 4 * 2 ^ T * Real.log 2 := by
    have h1 : (2 * (T + 1) + 4 * 2 ^ T) * Real.log 2 =
        2 * ((T + 1) * Real.log 2) + 4 * 2 ^ T * Real.log 2 := by ring
    rw [hD]; linarith
  have hED : Ex * D * L ≤ 16 * (ℓ + 1) * x := by
    calc Ex * D * L ≤ Ex * (4 * 2 ^ T * Real.log 2) * L := by gcongr
      _ = 4 * Real.log 2 * (Ex * (2 ^ T * L)) := by ring
      _ ≤ 4 * Real.log 2 * (4 * (T + 1) * x) := by gcongr
      _ = 16 * ((T + 1) * Real.log 2) * x := by ring
      _ ≤ 16 * (ℓ + 1) * x := by gcongr
  -- `16 (ℓ+1) L ≤ (16 + ε) ℓ D`
  have hfin : 16 * (ℓ + 1) * L ≤ (16 + ε) * ℓ * D := by
    have hε' : ε = 16 * δ := by rw [hδ]; ring
    rw [hε', hD]
    have h1 : 2 * L ≤ δ * ℓ * L := mul_le_mul_of_nonneg_right hℓδ hL0.le
    have h2 : 4 * (1 + δ) * (ℓ + 1) * ℓ ≤ δ * L * ℓ := mul_le_mul_of_nonneg_right hkey hℓ0.le
    have h3 : (16 + 16 * δ) * ℓ * (L - 2 * (ℓ + 1)) - 16 * (ℓ + 1) * L =
        8 * (δ * ℓ * L - 2 * L) + 8 * (δ * L * ℓ - 4 * (1 + δ) * (ℓ + 1) * ℓ) := by ring
    nlinarith
  rw [le_div_iff₀ (by positivity)]
  have h3 : Ex * L ^ 2 * D ≤ (16 + ε) * x * ℓ * D := by
    calc Ex * L ^ 2 * D = (Ex * D * L) * L := by ring
      _ ≤ 16 * (ℓ + 1) * x * L := by gcongr
      _ = x * (16 * (ℓ + 1) * L) := by ring
      _ ≤ x * ((16 + ε) * ℓ * D) := by gcongr
      _ = (16 + ε) * x * ℓ * D := by ring
  exact le_of_mul_le_mul_right h3 hDpos

end ElitePrimes
