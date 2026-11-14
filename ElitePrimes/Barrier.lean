import ElitePrimes.GRH

/-!
# Section 6: why the method stops (Theorem 6.1)

The prime number theorem for arithmetic progressions with the GRH error term,
`π(x; q, a) = li(x)/φ(q) + O(√x log x)` uniformly for `q ≤ x`, is not in mathlib. It is an
explicit ASSUMPTION here (`GRHPrimesInAP`). Everything else is proved.

We use `li x = ∫_2^x dt / log t`; it differs from the other usual normalization by the
constant `li 2`, which is absorbed by the error term.

* `MT T`, `Sset T N`   : `M_T = 2^T ∏_{1 ≤ n < T} F n` and `S_T(N)`.
* `card_Sset`          : `#S_T(N) = ∑_{1 ≤ e < T} ∑_{a ∈ R_e} π(N; M_e, a) + π(N; 2^T, 1)`.
* `barrier_main`       : **Theorem 6.1**, first statement.
* `barrier_asymp`      : **Theorem 6.1**, second statement.
-/

namespace ElitePrimes

open Nat Finset

/-- `li x = ∫_2^x dt / log t`. -/
noncomputable def li (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t

/-- The prime number theorem for arithmetic progressions under GRH (ASSUMED):
`|π(x; q, a) - li(x)/φ(q)| ≤ C √x log x` for `x ≥ 2`, `1 ≤ q ≤ x`, `gcd(a, q) = 1`. -/
def GRHPrimesInAP : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (q a : ℕ) (x : ℝ), 2 ≤ x → 1 ≤ q → (q : ℝ) ≤ x → Nat.Coprime a q →
    |(primesInAP ⌊x⌋₊ q a : ℝ) - li x / q.totient| ≤ C * Real.sqrt x * Real.log x

/-- `M_T = 2^T ∏_{n=1}^{T-1} F n`. -/
def MT (T : ℕ) : ℕ := 2 ^ T * ∏ n ∈ Ico 1 T, F n

/-- `S_T(N)`: the odd primes `p ≤ N` with `J(p | F n) = -1` for every `e_p ≤ n < T`. -/
noncomputable def Sset (T N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ ∀ n ∈ Ico (ev p) T, jacobiSym p (F n) = -1)

/-- The primes `p ≤ N` with `e_p = e` and `J(p | F n) = -1` for `e ≤ n < T`. -/
noncomputable def piece (e T N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun p => p.Prime ∧ ev p = e ∧ ∀ n ∈ Ico e T, jacobiSym p (F n) = -1)

/-- The primes `p ≤ N` with `p ≡ a (mod q)`; its cardinality is `primesInAP N q a`. -/
def cls (N q a : ℕ) : Finset ℕ := (range (N + 1)).filter (fun p => p.Prime ∧ p % q = a % q)

theorem ev_two : ev 2 = 0 := by simp [ev]

theorem MT_pos (T : ℕ) : 0 < MT T := Nat.mul_pos (by positivity) (prod_pos (fun n _ => F_pos n))

theorem Me_le_MT {e T : ℕ} (he : 1 ≤ e) (heT : e < T) : Me e T ≤ MT T := by
  apply Nat.le_of_dvd (MT_pos T)
  apply mul_dvd_mul (Nat.pow_dvd_pow 2 heT)
  apply prod_dvd_prod_of_subset
  intro n hn
  simp only [mem_Ico] at hn ⊢
  omega

/-- `piece e T N` is the union of the classes `a mod M_e`, `a ∈ R_e`. -/
theorem piece_eq {e T N : ℕ} (he : 1 ≤ e) :
    piece e T N = (Rset e T).biUnion (fun u => cls N (Me e T) (u : ZMod (Me e T)).val) := by
  classical
  ext p
  simp only [piece, cls, mem_filter, mem_biUnion, mem_range]
  constructor
  · rintro ⟨hpN, hpp, hev, hJ⟩
    have hp2 : p ≠ 2 := by rintro rfl; rw [ev_two] at hev; omega
    have hcop : Nat.Coprime p (Me e T) := by
      show Nat.Coprime p (2 ^ (e + 1) * Pe e T)
      apply Nat.Coprime.mul_right
      · apply Nat.Coprime.pow_right
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
        intro h2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).mp h2).symm
      · apply Nat.Coprime.prod_right
        intro n hn
        haveI : NeZero (F n) := ⟨(F_pos n).ne'⟩
        have hg : Int.gcd (p : ℤ) (F n) = 1 := by
          by_contra hne
          have h0 := (jacobiSym.eq_zero_iff_not_coprime).mpr hne
          rw [hJ n hn] at h0
          norm_num at h0
        rwa [Int.gcd_natCast_natCast] at hg
    refine ⟨ZMod.unitOfCoprime p hcop, ?_, hpN, hpp, ?_⟩
    · simp only [Rset, mem_filter, mem_univ, true_and, sig, Prod.mk.injEq]
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      constructor
      · rw [Nat.mod_mod_of_dvd _ (two_pow_dvd_Me e T), ← hev]
        exact mod_pow_ev hpp hp2
      · apply Finset.filter_true_of_mem
        intro n hn
        rw [jacobi_congr ((Nat.mod_modEq p (Me e T)).of_dvd (F_dvd_Me hn))]
        exact hJ n hn
    · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_mod]
  · rintro ⟨u, hu, hpN, hpp, hpu⟩
    simp only [Rset, mem_filter, mem_univ, true_and, sig, Prod.mk.injEq] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hpu' : p % Me e T = (u : ZMod (Me e T)).val := by
      rw [hpu, Nat.mod_eq_of_lt (ZMod.val_lt _)]
    refine ⟨hpN, hpp, ?_, ?_⟩
    · apply ev_eq_of_mod
      rw [← Nat.mod_mod_of_dvd p (two_pow_dvd_Me e T), hpu', hu1]
    · intro n hn
      have hmem : n ∈ (Ico e T).filter
          (fun n => jacobiSym ((u : ZMod (Me e T)).val : ℤ) (F n) = -1) := by
        rw [hu2]; exact hn
      rw [jacobi_congr ((Nat.mod_modEq p (Me e T)).symm.of_dvd (F_dvd_Me hn)), hpu']
      exact (mem_filter.mp hmem).2

theorem card_piece {e T N : ℕ} (he : 1 ≤ e) :
    (piece e T N).card = ∑ u ∈ Rset e T, primesInAP N (Me e T) (u : ZMod (Me e T)).val := by
  classical
  rw [piece_eq he, card_biUnion]
  · rfl
  · intro u _ v _ huv
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpu hpv
    simp only [cls, mem_filter] at hpu hpv
    apply huv
    apply Units.ext
    apply ZMod.val_injective
    rw [← Nat.mod_eq_of_lt (ZMod.val_lt (u : ZMod (Me e T))),
      ← Nat.mod_eq_of_lt (ZMod.val_lt (v : ZMod (Me e T))), ← hpu.2.2, ← hpv.2.2]

/-- The primes `p ≤ N` with `e_p ≥ T`, i.e. `p ≡ 1 (mod 2^T)` (for `T ≥ 2`). -/
theorem card_pieceT {T N : ℕ} (hT : 2 ≤ T) :
    ((range (N + 1)).filter (fun p => p.Prime ∧ T ≤ ev p)).card = primesInAP N (2 ^ T) 1 := by
  unfold primesInAP
  congr 1
  apply filter_congr
  intro p _
  have h4 : 4 ≤ 2 ^ T := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hT)
  have h1 : 1 % 2 ^ T = 1 := Nat.mod_eq_of_lt (by omega)
  constructor
  · rintro ⟨hpp, hTe⟩
    exact ⟨hpp, mod_pow_of_le_ev hpp hTe⟩
  · rintro ⟨hpp, hpm⟩
    refine ⟨hpp, ?_⟩
    rw [h1] at hpm
    have hp2 := hpp.two_le
    have hne : p - 1 ≠ 0 := by
      intro h0
      have : p = 2 := by omega
      subst this
      rw [Nat.mod_eq_of_lt (by omega)] at hpm
      omega
    have hdvd : 2 ^ T ∣ p - 1 :=
      (Nat.modEq_iff_dvd' (by omega)).mp (by show 1 % 2 ^ T = p % 2 ^ T; rw [h1, hpm])
    exact (padicValNat_dvd_iff_le hne).mp hdvd

/-- `#S_T(N) = ∑_{1 ≤ e < T} #piece e + #{p ≤ N : e_p ≥ T}`. -/
theorem card_Sset {T N : ℕ} (hT : 1 ≤ T) :
    (Sset T N).card = ∑ e ∈ Ico 1 T, (piece e T N).card +
      ((range (N + 1)).filter (fun p => p.Prime ∧ T ≤ ev p)).card := by
  classical
  have hdecomp : Sset T N = (Ico 1 T).biUnion (fun e => piece e T N) ∪
      (range (N + 1)).filter (fun p => p.Prime ∧ T ≤ ev p) := by
    ext p
    simp only [Sset, piece, mem_union, mem_biUnion, mem_filter, mem_Ico, mem_range]
    constructor
    · rintro ⟨hpN, hpp, hp2, hJ⟩
      have h1 := one_le_ev hpp hp2
      by_cases hlt : ev p < T
      · exact Or.inl ⟨ev p, ⟨h1, hlt⟩, hpN, hpp, rfl, hJ⟩
      · exact Or.inr ⟨hpN, hpp, not_lt.mp hlt⟩
    · rintro (⟨e, ⟨he1, _⟩, hpN, hpp, hev, hJ⟩ | ⟨hpN, hpp, hTe⟩)
      · refine ⟨hpN, hpp, ?_, by rw [hev]; exact hJ⟩
        rintro rfl; rw [ev_two] at hev; omega
      · refine ⟨hpN, hpp, ?_, ?_⟩
        · rintro rfl; rw [ev_two] at hTe; omega
        · intro n hn; omega
  rw [hdecomp, card_union_of_disjoint, card_biUnion]
  · intro e _ f _ hef
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpe hpf
    simp only [piece, mem_filter] at hpe hpf
    exact hef (hpe.2.2.1.symm.trans hpf.2.2.1)
  · rw [Finset.disjoint_left]
    intro p hp hpT
    simp only [mem_biUnion, piece, mem_filter, mem_Ico] at hp hpT
    obtain ⟨e, ⟨_, heT⟩, _, _, hev, _⟩ := hp
    omega

/-- `x^(1/3) √x = x^(5/6)`. -/
theorem rpow_third_mul_sqrt {x : ℝ} (hx : 0 < x) :
    x ^ ((1 : ℝ) / 3) * Real.sqrt x = x ^ ((5 : ℝ) / 6) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]; norm_num

/-- **Theorem 6.1**, first statement. Assuming the GRH prime number theorem for arithmetic
progressions, there is an absolute `C` such that for `T ≥ 2`, `x ≥ 2` and `M_T ≤ x^(1/3)`,
`|#S_T(x) - (T+1)/2^T · li(x)| ≤ C x^(5/6) log x`. -/
theorem barrier_main (hGRH : GRHPrimesInAP) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, 2 ≤ T → ∀ x : ℝ, 2 ≤ x → (MT T : ℝ) ≤ x ^ ((1 : ℝ) / 3) →
      |((Sset T ⌊x⌋₊).card : ℝ) - (T + 1) / 2 ^ T * li x| ≤
        C * x ^ ((5 : ℝ) / 6) * Real.log x := by
  classical
  obtain ⟨C₀, hC₀, hG⟩ := hGRH
  refine ⟨2 * C₀, by positivity, fun T hT x hx hM => ?_⟩
  set N := ⌊x⌋₊ with hNdef
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  set δ := C₀ * Real.sqrt x * Real.log x with hδdef
  have hδ : 0 ≤ δ := mul_nonneg (mul_nonneg hC₀ (Real.sqrt_nonneg _)) hlog0
  have hMx : (MT T : ℝ) ≤ x := by
    refine le_trans hM ?_
    calc x ^ ((1 : ℝ) / 3) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = x := Real.rpow_one x
  have h2T : 2 ^ T ≤ MT T := Nat.le_mul_of_pos_right _ (prod_pos (fun n _ => F_pos n))
  -- each block `e_p = e`
  have hpiece : ∀ e ∈ Ico 1 T,
      |((piece e T N).card : ℝ) - li x / 2 ^ T| ≤ (Rset e T).card * δ := by
    intro e he
    obtain ⟨he1, heT⟩ := mem_Ico.mp he
    have hR : ((Rset e T).card : ℝ) * 2 ^ T = (Me e T).totient := by
      exact_mod_cast card_R_mul he1 heT.le
    have hφ : (0 : ℝ) < (Me e T).totient := by exact_mod_cast Nat.totient_pos.mpr (Me_pos e T)
    have hR0 : ((Rset e T).card : ℝ) ≠ 0 := by
      intro h; rw [h, zero_mul] at hR; linarith
    have hli : li x / 2 ^ T = ∑ u ∈ Rset e T, li x / (Me e T).totient := by
      rw [sum_const, nsmul_eq_mul, ← hR]
      field_simp
    have hMeX : ((Me e T : ℕ) : ℝ) ≤ x :=
      le_trans (by exact_mod_cast Me_le_MT he1 heT) hMx
    rw [card_piece he1, hli]
    push_cast
    rw [← sum_sub_distrib]
    calc |∑ u ∈ Rset e T, ((primesInAP N (Me e T) (u : ZMod (Me e T)).val : ℝ) -
            li x / (Me e T).totient)|
        ≤ ∑ u ∈ Rset e T, |(primesInAP N (Me e T) (u : ZMod (Me e T)).val : ℝ) -
            li x / (Me e T).totient| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ u ∈ Rset e T, δ := sum_le_sum (fun u _ =>
          hG _ _ x hx (Me_pos e T) hMeX (ZMod.val_coe_unit_coprime u))
      _ = (Rset e T).card * δ := by rw [sum_const, nsmul_eq_mul]
  -- the block `e_p ≥ T`
  have hpieceT : |(((range (N + 1)).filter (fun p => p.Prime ∧ T ≤ ev p)).card : ℝ) -
      li x / 2 ^ (T - 1)| ≤ δ := by
    rw [card_pieceT hT]
    have h := hG (2 ^ T) 1 x hx Nat.one_le_two_pow
      (le_trans (by exact_mod_cast h2T) hMx) (Nat.coprime_one_left _)
    rwa [Nat.totient_prime_pow Nat.prime_two (by omega), show 2 - 1 = 1 from rfl, mul_one,
      Nat.cast_pow, Nat.cast_ofNat] at h
  -- `|R_e| ≤ M_T / 2^T`
  have hR_le : ∀ e ∈ Ico 1 T, ((Rset e T).card : ℝ) ≤ MT T / 2 ^ T := by
    intro e he
    obtain ⟨he1, heT⟩ := mem_Ico.mp he
    rw [le_div_iff₀ (by positivity)]
    have h1 : (Rset e T).card * 2 ^ T ≤ MT T :=
      (card_R_mul he1 heT.le).le.trans ((Nat.totient_le _).trans (Me_le_MT he1 heT))
    exact_mod_cast h1
  -- assembling
  have h2 : (2 : ℝ) ^ T = 2 * 2 ^ (T - 1) := by
    have hT' : T = (T - 1) + 1 := by omega
    conv_lhs => rw [hT']
    rw [pow_succ]; ring
  have hsum : ((Sset T N).card : ℝ) - (T + 1) / 2 ^ T * li x =
      ∑ e ∈ Ico 1 T, (((piece e T N).card : ℝ) - li x / 2 ^ T) +
        ((((range (N + 1)).filter (fun p => p.Prime ∧ T ≤ ev p)).card : ℝ) -
          li x / 2 ^ (T - 1)) := by
    rw [card_Sset (by omega)]
    push_cast
    rw [sum_sub_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ T),
      h2]
    field_simp
    ring
  have hTle : ((T : ℝ) - 1) ≤ 2 ^ T := by
    have : (T : ℝ) ≤ 2 ^ T := by exact_mod_cast Nat.lt_two_pow_self.le
    linarith
  have hM1 : (1 : ℝ) ≤ MT T := by exact_mod_cast MT_pos T
  rw [hsum]
  calc |∑ e ∈ Ico 1 T, (((piece e T N).card : ℝ) - li x / 2 ^ T) +
        ((((range (N + 1)).filter (fun p => p.Prime ∧ T ≤ ev p)).card : ℝ) -
          li x / 2 ^ (T - 1))|
      ≤ ∑ e ∈ Ico 1 T, |((piece e T N).card : ℝ) - li x / 2 ^ T| +
          |(((range (N + 1)).filter (fun p => p.Prime ∧ T ≤ ev p)).card : ℝ) -
            li x / 2 ^ (T - 1)| :=
        (abs_add_le _ _).trans (_root_.add_le_add (abs_sum_le_sum_abs _ _) le_rfl)
    _ ≤ ∑ e ∈ Ico 1 T, (MT T / 2 ^ T) * δ + δ :=
        _root_.add_le_add (sum_le_sum fun e he =>
          (hpiece e he).trans (mul_le_mul_of_nonneg_right (hR_le e he) hδ)) hpieceT
    _ = ((T : ℝ) - 1) / 2 ^ T * MT T * δ + δ := by
        rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ T)]
        push_cast
        ring
    _ ≤ 1 * MT T * δ + MT T * δ := by
        gcongr
        · rw [div_le_one (by positivity)]; exact hTle
        · nlinarith
    _ = 2 * C₀ * ((MT T : ℝ) * Real.sqrt x) * Real.log x := by rw [hδdef]; ring
    _ ≤ 2 * C₀ * (x ^ ((1 : ℝ) / 3) * Real.sqrt x) * Real.log x := by gcongr
    _ = 2 * C₀ * x ^ ((5 : ℝ) / 6) * Real.log x := by rw [rpow_third_mul_sqrt hx0]

theorem intervalIntegrable_inv_log {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  apply ContinuousOn.div continuousOn_const
  · apply Real.continuousOn_log.mono
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [ht.1]
  · intro t ht
    exact (Real.log_pos (by linarith [ht.1])).ne'

/-- `∫_a^b dt / log t ≤ (b - a) / log a` for `2 ≤ a ≤ b`. -/
theorem integral_inv_log_le {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / Real.log t ≤ (b - a) / Real.log a := by
  have h := intervalIntegral.integral_mono_on hab (intervalIntegrable_inv_log ha hab)
    (intervalIntegrable_const (c := 1 / Real.log a)) (fun t ht => by
      have hla : 0 < Real.log a := Real.log_pos (by linarith)
      exact one_div_le_one_div_of_le hla (Real.log_le_log (by linarith) ht.1))
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith [show (b - a) * (1 / Real.log a) = (b - a) / Real.log a by ring]

/-- `li x ≥ (x - 2) / log x` for `x ≥ 2`. -/
theorem li_lower {x : ℝ} (hx : 2 ≤ x) : (x - 2) / Real.log x ≤ li x := by
  have h := intervalIntegral.integral_mono_on hx
    (intervalIntegrable_const (c := 1 / Real.log x)) (intervalIntegrable_inv_log le_rfl hx)
    (fun t ht => by
      have hlt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      exact one_div_le_one_div_of_le hlt (Real.log_le_log (by linarith [ht.1]) ht.2))
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  unfold li
  linarith [show (x - 2) * (1 / Real.log x) = (x - 2) / Real.log x by ring]

/-- `li x ≤ 2 √x + 2x / log x` for `x ≥ 4`. -/
theorem li_upper {x : ℝ} (hx : 4 ≤ x) : li x ≤ 2 * Real.sqrt x + 2 * x / Real.log x := by
  have hs2 : 2 ≤ Real.sqrt x := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hsx : Real.sqrt x ≤ x := by
    have := Real.sqrt_le_sqrt hx
    nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ x by linarith)]
  unfold li
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_inv_log le_rfl hs2) (intervalIntegrable_inv_log hs2 hsx)]
  have h1 := integral_inv_log_le le_rfl hs2
  have h2 := integral_inv_log_le hs2 hsx
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hls : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt (by linarith)
  rw [hls] at h2
  have h3 : (Real.sqrt x - 2) / Real.log 2 ≤ 2 * Real.sqrt x := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h4 : (x - Real.sqrt x) / (Real.log x / 2) ≤ 2 * x / Real.log x := by
    rw [div_le_div_iff₀ (by positivity) hL]; nlinarith
  linarith

theorem log_six_lt_two : Real.log 6 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [h]
  nlinarith [Real.exp_one_gt_d9]

/-- **Theorem 6.1**, second statement. Assuming the GRH prime number theorem for arithmetic
progressions: for all large `x` and every `T ≥ 2` with `M_T ≤ x^(1/3) < M_(T+1)` (that is,
`T` is the largest integer with `M_T ≤ x^(1/3)`), we have `log x / 12 < 2^T ≤ 2 log x` and
`x log log x / (16 (log x)^2) ≤ #S_T(x) ≤ 109 x log log x / (log x)^2`. -/
theorem barrier_asymp (hGRH : GRHPrimesInAP) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ T : ℕ, 2 ≤ T → (MT T : ℝ) ≤ x ^ ((1 : ℝ) / 3) →
      x ^ ((1 : ℝ) / 3) < MT (T + 1) →
      Real.log x / 12 < 2 ^ T ∧ (2 : ℝ) ^ T ≤ 2 * Real.log x ∧
      x * Real.log (Real.log x) / (16 * Real.log x ^ 2) ≤ ((Sset T ⌊x⌋₊).card : ℝ) ∧
      ((Sset T ⌊x⌋₊).card : ℝ) ≤ 109 * x * Real.log (Real.log x) / Real.log x ^ 2 := by
  obtain ⟨C, hC, hmain⟩ := barrier_main hGRH
  set K : ℝ := 16 * C * 36 ^ 3 + 2 with hK
  have ev1 : ∀ᶠ x in Filter.atTop, (4 : ℝ) ≤ Real.log (Real.log x) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 4
  have ev2 : ∀ᶠ x in Filter.atTop, K ≤ x ^ ((1 : ℝ) / 36) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop K
  have ev3 : ∀ᶠ x in Filter.atTop, (4 : ℝ) ≤ x := Filter.eventually_ge_atTop 4
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp (ev1.and (ev2.and ev3))
  refine ⟨x₀, fun x hx T hT hM hM1 => ?_⟩
  obtain ⟨hℓ4, hwK, hx4⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hS := hmain T hT x (by linarith) hM
  set L := Real.log x with hLdef
  set ℓ := Real.log L with hℓdef
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hlog3 : Real.log (x ^ ((1 : ℝ) / 3)) = L / 3 := by rw [Real.log_rpow hx0]; ring
  have h2T : (2 : ℝ) ^ T = 2 * 2 ^ (T - 1) := by
    have hT' : T = (T - 1) + 1 := by omega
    conv_lhs => rw [hT']
    rw [pow_succ]; ring
  -- (a) `2^T ≤ 2 log x`, since `2^(2^(T-1)) < F_(T-1) ≤ M_T ≤ x^(1/3)`
  have hFT : (2 : ℝ) ^ (2 ^ (T - 1)) < MT T := by
    have h1 : F (T - 1) ∣ ∏ n ∈ Ico 1 T, F n :=
      dvd_prod_of_mem F (mem_Ico.mpr ⟨by omega, by omega⟩)
    have h2 : F (T - 1) ≤ MT T :=
      le_trans (Nat.le_of_dvd (prod_pos fun n _ => F_pos n) h1)
        (Nat.le_mul_of_pos_left _ (by positivity))
    have h3 : 2 ^ (2 ^ (T - 1)) < F (T - 1) := by rw [F_def]; omega
    exact_mod_cast lt_of_lt_of_le h3 h2
  have hup : (2 : ℝ) ^ T ≤ 2 * L := by
    have h1 : (2 : ℝ) ^ (2 ^ (T - 1)) < x ^ ((1 : ℝ) / 3) := lt_of_lt_of_le hFT hM
    have h2 := Real.log_lt_log (by positivity) h1
    rw [Real.log_pow, hlog3] at h2
    push_cast at h2
    have h4 : (2 : ℝ) ^ (T - 1) * (1 / 2) ≤ 2 ^ (T - 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  -- (b) `log x / 12 < 2^T`, since `x^(1/3) < M_(T+1) < 2^(T+1) 2^(2^(T+1))`
  have hlow : L / 12 < (2 : ℝ) ^ T := by
    have h1 : (MT (T + 1) : ℝ) < 2 ^ (T + 1 + 2 ^ (T + 1)) := by
      have h' : MT (T + 1) < 2 ^ (T + 1) * 2 ^ (2 ^ (T + 1)) :=
        Nat.mul_lt_mul_of_pos_left (prod_F_Ico_lt 1 (T + 1)) (by positivity)
      rw [pow_add]
      exact_mod_cast h'
    have h2 := Real.log_lt_log (by positivity) (lt_trans hM1 h1)
    rw [Real.log_pow, hlog3] at h2
    push_cast at h2
    have h3 : ((T : ℝ) + 1) ≤ 2 ^ (T + 1) := by
      have := (Nat.lt_two_pow_self (n := T + 1)).le
      exact_mod_cast this
    have h4 : ((T : ℝ) + 1 + 2 ^ (T + 1)) * Real.log 2 ≤ ((T : ℝ) + 1 + 2 ^ (T + 1)) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h5 : (2 : ℝ) ^ (T + 1) = 2 * 2 ^ T := by rw [pow_succ]; ring
    linarith
  -- (c) `ℓ / 2 ≤ T + 1 ≤ 3 ℓ`, with `ℓ = log log x`
  have hT_up : (T : ℝ) + 1 ≤ 3 * ℓ := by
    have h1 := Real.log_le_log (by positivity) hup
    rw [Real.log_pow, Real.log_mul (by norm_num) hL0.ne'] at h1
    have h2 : (T : ℝ) * (1 / 2) ≤ T * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hT_low : ℓ / 2 ≤ (T : ℝ) + 1 := by
    have h1 : L / 6 < (2 : ℝ) ^ (T + 1) := by rw [pow_succ]; linarith
    have h2 := Real.log_lt_log (by positivity) h1
    rw [Real.log_pow, Real.log_div hL0.ne' (by norm_num)] at h2
    push_cast at h2
    have h3 : ((T : ℝ) + 1) * Real.log 2 ≤ ((T : ℝ) + 1) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h4 := log_six_lt_two
    linarith
  -- `w = x^(1/36)`
  set w := x ^ ((1 : ℝ) / 36) with hwdef
  have hw0 : 0 < w := Real.rpow_pos_of_pos hx0 _
  have hw36 : w ^ 36 = x := by
    rw [hwdef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hC3 : 0 ≤ 16 * C * 36 ^ 3 := by positivity
  have hK2 : 2 ≤ K := by rw [hK]; linarith
  have hw2 : 2 ≤ w := le_trans hK2 hwK
  have hLw : L = 36 * Real.log w := by rw [hLdef, ← hw36, Real.log_pow]; norm_num
  have hlogw : Real.log w ≤ w := le_trans (Real.log_le_sub_one_of_pos hw0) (by linarith)
  have hL36 : L ≤ 36 * w := by linarith
  have hsqrt : Real.sqrt x = w ^ 18 := by
    rw [← hw36, show w ^ 36 = (w ^ 18) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have h56 : x ^ ((5 : ℝ) / 6) = w ^ 30 := by
    rw [← hw36, ← Real.rpow_natCast w 36, ← Real.rpow_mul hw0.le, ← Real.rpow_natCast w 30]
    norm_num
  -- (d) the error term is at most `x ℓ / (16 L^2)`
  have herr : C * x ^ ((5 : ℝ) / 6) * L ≤ x * ℓ / (16 * L ^ 2) := by
    rw [le_div_iff₀ (by positivity), h56]
    have hw3 : 16 * C * 36 ^ 3 ≤ w ^ 3 := by
      have : w ≤ w ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
      linarith
    calc C * w ^ 30 * L * (16 * L ^ 2) = 16 * C * w ^ 30 * L ^ 3 := by ring
      _ ≤ 16 * C * w ^ 30 * (36 * w) ^ 3 := by gcongr
      _ = (16 * C * 36 ^ 3) * w ^ 33 := by ring
      _ ≤ w ^ 3 * w ^ 33 := by gcongr
      _ = x := by rw [← hw36]; ring
      _ ≤ x * ℓ := le_mul_of_one_le_right hx0.le (by linarith)
  -- (e) `x / (2L) ≤ li x ≤ 3x / L`
  have hli_lo : x / (2 * L) ≤ li x := by
    refine le_trans ?_ (li_lower (by linarith))
    rw [div_le_div_iff₀ (by positivity) hL0]
    nlinarith
  have hli_up : li x ≤ 3 * x / L := by
    have h1 := li_upper hx4
    have h2 : 2 * Real.sqrt x ≤ x / L := by
      rw [le_div_iff₀ hL0, hsqrt]
      have h17 : (72 : ℝ) ≤ w ^ 17 :=
        le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hw2 17)
      calc 2 * w ^ 18 * L ≤ 2 * w ^ 18 * (36 * w) := by gcongr
        _ = 72 * w ^ 19 := by ring
        _ ≤ w ^ 17 * w ^ 19 := by gcongr
        _ = x := by rw [← hw36]; ring
    have h3 : 2 * x / L + x / L = 3 * x / L := by ring
    linarith
  -- (f) the main term `(T+1)/2^T · li x`
  have hr_up : ((T : ℝ) + 1) / 2 ^ T ≤ 36 * ℓ / L := by
    rw [div_le_div_iff₀ (by positivity) hL0]
    calc ((T : ℝ) + 1) * L ≤ 3 * ℓ * L := by gcongr
      _ ≤ 3 * ℓ * (12 * 2 ^ T) := by gcongr; linarith
      _ = 36 * ℓ * 2 ^ T := by ring
  have hr_lo : ℓ / (4 * L) ≤ ((T : ℝ) + 1) / 2 ^ T := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc ℓ * 2 ^ T ≤ (2 * ((T : ℝ) + 1)) * 2 ^ T := by gcongr; linarith
      _ ≤ (2 * ((T : ℝ) + 1)) * (2 * L) := by gcongr
      _ = ((T : ℝ) + 1) * (4 * L) := by ring
  have hli0 : 0 ≤ li x := le_trans (by positivity) hli_lo
  have hM_up : ((T : ℝ) + 1) / 2 ^ T * li x ≤ 108 * (x * ℓ / L ^ 2) := by
    calc ((T : ℝ) + 1) / 2 ^ T * li x ≤ 36 * ℓ / L * (3 * x / L) :=
          mul_le_mul hr_up hli_up hli0 (by positivity)
      _ = 108 * (x * ℓ / L ^ 2) := by field_simp; ring
  have hM_lo : 2 * (x * ℓ / (16 * L ^ 2)) ≤ ((T : ℝ) + 1) / 2 ^ T * li x := by
    calc 2 * (x * ℓ / (16 * L ^ 2)) = ℓ / (4 * L) * (x / (2 * L)) := by field_simp; ring
      _ ≤ ((T : ℝ) + 1) / 2 ^ T * li x := mul_le_mul hr_lo hli_lo (by positivity) (by positivity)
  obtain ⟨hS1, hS2⟩ := abs_sub_le_iff.mp (le_trans hS herr)
  have hsmall : x * ℓ / (16 * L ^ 2) ≤ x * ℓ / L ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith
  refine ⟨hlow, hup, by linarith, ?_⟩
  have h109 : 109 * x * ℓ / L ^ 2 = 109 * (x * ℓ / L ^ 2) := by ring
  rw [h109]
  linarith

end ElitePrimes
