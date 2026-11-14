import ElitePrimes.Lemma4
import ElitePrimes.TheoremA

/-!
# Lemma 5.4 (final bound) and Corollary 5.5

* `geom_low`, `geom_high` : the two geometric series in the proof of Lemma 5.4.
* `sum_min_le`            : `∑_s min(2^s d, N/(2^s d)) ≤ 4 √N`.
* `card_dv_eq_le_sqrt`    : `#{p ≤ N : d_p = d} ≤ 4 √N`.
* `card_dv_le_nat`, `card_dv_le` : **Lemma 5.4**, `#{p ≤ x : d_p ≤ y} ≤ 2 (y + 1) √x`.
* `cor_oddpart`           : **Corollary 5.5**.
-/

namespace ElitePrimes

open Nat Finset

/-- The terms `r 2^s ≤ 1` of a geometric series sum to at most `2`. -/
theorem geom_low {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∑ s ∈ (range n).filter (fun s => r * 2 ^ s ≤ 1), r * 2 ^ s ≤ 2 := by
  have key : ∀ n, (∑ s ∈ (range n).filter (fun s => r * 2 ^ s ≤ 1), r * 2 ^ s) ≤ 2 ∧
      (∑ s ∈ (range n).filter (fun s => r * 2 ^ s ≤ 1), r * 2 ^ s) + r ≤ r * 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs : r * 2 ^ (n + 1) = 2 * (r * 2 ^ n) := by ring
      have hpos : 0 < r * 2 ^ n := by positivity
      rw [range_add_one, filter_insert, hs]
      split_ifs with h
      · rw [sum_insert (by simp)]
        constructor <;> linarith [ih.2]
      · constructor <;> linarith [ih.1, ih.2]
  exact (key n).1

/-- The terms `1 / (r 2^s)` with `r 2^s > 1` sum to at most `2`. -/
theorem geom_high {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∑ s ∈ (range n).filter (fun s => ¬ r * 2 ^ s ≤ 1), (r * 2 ^ s)⁻¹ ≤ 2 := by
  have key : ∀ n, (∑ s ∈ (range n).filter (fun s => ¬ r * 2 ^ s ≤ 1), (r * 2 ^ s)⁻¹) = 0 ∨
      (∑ s ∈ (range n).filter (fun s => ¬ r * 2 ^ s ≤ 1), (r * 2 ^ s)⁻¹) +
        2 * (r * 2 ^ n)⁻¹ ≤ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hpos : 0 < r * 2 ^ n := by positivity
      have hs : 2 * (r * 2 ^ (n + 1))⁻¹ = (r * 2 ^ n)⁻¹ := by
        rw [pow_succ]; field_simp
      have hinv : 0 < (r * 2 ^ n)⁻¹ := inv_pos.mpr hpos
      rw [range_add_one, filter_insert, hs]
      split_ifs with h
      · rcases ih with h0 | h0
        · left; exact h0
        · right; linarith
      · right
        rw [sum_insert (by simp)]
        have h1 : (r * 2 ^ n)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (lt_of_not_ge h)
        rcases ih with h0 | h0
        · rw [h0]; linarith
        · linarith
  rcases key n with h0 | h0
  · rw [h0]; norm_num
  · have : 0 < (r * 2 ^ n)⁻¹ := inv_pos.mpr (by positivity)
    linarith

/-- Lemma 5.4, geometric-series step: `∑_s min(2^s d, N/(2^s d)) ≤ 4 √N`. -/
theorem sum_min_le (N d : ℕ) (hd : 0 < d) :
    ((∑ s ∈ range (N + 1), min (2 ^ s * d) (N / (2 ^ s * d)) : ℕ) : ℝ) ≤ 4 * Real.sqrt N := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  set q := Real.sqrt N with hqdef
  have hq : 0 < q := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hqq : q * q = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  set r : ℝ := d / q with hrdef
  have hr : 0 < r := div_pos (by exact_mod_cast hd) hq
  have hterm : ∀ s, ((min (2 ^ s * d) (N / (2 ^ s * d)) : ℕ) : ℝ) ≤
      q * ((if r * 2 ^ s ≤ 1 then r * 2 ^ s else 0) +
        (if ¬ r * 2 ^ s ≤ 1 then (r * 2 ^ s)⁻¹ else 0)) := by
    intro s
    have ha : ((2 ^ s * d : ℕ) : ℝ) = q * (r * 2 ^ s) := by
      push_cast
      rw [hrdef]
      field_simp
    by_cases h : r * 2 ^ s ≤ 1
    · rw [ite_eq_left h, ite_eq_right (not_not.mpr h), add_zero, ← ha]
      exact_mod_cast Nat.min_le_left _ _
    · rw [ite_eq_right h, ite_eq_left h, zero_add]
      calc ((min (2 ^ s * d) (N / (2 ^ s * d)) : ℕ) : ℝ)
          ≤ ((N / (2 ^ s * d) : ℕ) : ℝ) := by exact_mod_cast Nat.min_le_right _ _
        _ ≤ (N : ℝ) / ((2 ^ s * d : ℕ) : ℝ) := Nat.cast_div_le
        _ = q * (r * 2 ^ s)⁻¹ := by
          rw [ha, ← hqq]
          have : 0 < r * 2 ^ s := by positivity
          field_simp
  rw [Nat.cast_sum]
  calc ∑ s ∈ range (N + 1), ((min (2 ^ s * d) (N / (2 ^ s * d)) : ℕ) : ℝ)
      ≤ ∑ s ∈ range (N + 1), q * ((if r * 2 ^ s ≤ 1 then r * 2 ^ s else 0) +
          (if ¬ r * 2 ^ s ≤ 1 then (r * 2 ^ s)⁻¹ else 0)) := sum_le_sum (fun s _ => hterm s)
    _ = q * (∑ s ∈ (range (N + 1)).filter (fun s => r * 2 ^ s ≤ 1), r * 2 ^ s +
          ∑ s ∈ (range (N + 1)).filter (fun s => ¬ r * 2 ^ s ≤ 1), (r * 2 ^ s)⁻¹) := by
        rw [← mul_sum, sum_add_distrib, sum_filter, sum_filter]
    _ ≤ q * (2 + 2) := by
        gcongr
        · exact geom_low hr _
        · exact geom_high hr _
    _ = 4 * Real.sqrt N := by rw [hqdef]; ring

/-- Lemma 5.4 for one odd part `d`: `#{p ≤ N : d_p = d} ≤ 4 √N`. -/
theorem card_dv_eq_le_sqrt (N d : ℕ) (hd : 0 < d) :
    (((range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ dv p = d)).card : ℝ) ≤
      4 * Real.sqrt N :=
  le_trans (by exact_mod_cast card_dv_eq_le N d hd) (sum_min_le N d hd)

/-- Lemma 5.4 at integers: `#{p ≤ N : d_p ≤ Y} ≤ 2 (Y + 1) √N` (odd primes `p`). -/
theorem card_dv_le_nat (N Y : ℕ) :
    (((range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ dv p ≤ Y)).card : ℝ) ≤
      2 * (Y + 1) * Real.sqrt N := by
  classical
  have hsub : (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ dv p ≤ Y) ⊆
      (range ((Y + 1) / 2)).biUnion (fun k =>
        (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ dv p = 2 * k + 1)) := by
    intro p hp
    simp only [mem_filter, mem_range] at hp
    obtain ⟨hpN, hpp, hp2, hle⟩ := hp
    haveI := Fact.mk hpp
    have hodd := dv_odd hp2
    rw [mem_biUnion]
    refine ⟨dv p / 2, ?_, ?_⟩
    · rw [mem_range]; omega
    · simp only [mem_filter, mem_range]
      exact ⟨hpN, hpp, hp2, by omega⟩
  have hcard := (card_le_card hsub).trans card_biUnion_le
  have hhalf : (((Y + 1) / 2 : ℕ) : ℝ) ≤ ((Y : ℝ) + 1) / 2 := by
    have := Nat.cast_div_le (α := ℝ) (m := Y + 1) (n := 2)
    push_cast at this
    exact this
  calc (((range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ dv p ≤ Y)).card : ℝ)
      ≤ ∑ k ∈ range ((Y + 1) / 2),
          (((range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ dv p = 2 * k + 1)).card : ℝ) := by
        exact_mod_cast hcard
    _ ≤ ∑ k ∈ range ((Y + 1) / 2), 4 * Real.sqrt N :=
        sum_le_sum (fun k _ => card_dv_eq_le_sqrt N _ (by omega))
    _ = (((Y + 1) / 2 : ℕ) : ℝ) * (4 * Real.sqrt N) := by
        rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ ((Y : ℝ) + 1) / 2 * (4 * Real.sqrt N) := by gcongr
    _ = 2 * (Y + 1) * Real.sqrt N := by ring

/-- **Lemma 5.4.** For real `x, y ≥ 0`, the odd primes `p ≤ x` with `d_p ≤ y` number at most
`2 (y + 1) √x`. -/
theorem card_dv_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (((range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ (dv p : ℝ) ≤ y)).card : ℝ) ≤
      2 * (y + 1) * Real.sqrt x := by
  classical
  have hset : (range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ (dv p : ℝ) ≤ y) =
      (range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ dv p ≤ ⌊y⌋₊) := by
    apply filter_congr
    intro p _
    rw [Nat.le_floor_iff hy]
  rw [hset]
  calc _ ≤ 2 * ((⌊y⌋₊ : ℝ) + 1) * Real.sqrt (⌊x⌋₊ : ℝ) := card_dv_le_nat _ _
    _ ≤ 2 * (y + 1) * Real.sqrt x := by
        gcongr
        · exact Nat.floor_le hy
        · exact Nat.floor_le hx

theorem mem_eliteSet {N p : ℕ} : p ∈ eliteSet N ↔ p ≤ N ∧ IsElite p := by
  classical
  simp [eliteSet]

/-- `(log t)^2 ≤ 16 √t` for `t ≥ 1`. -/
theorem log_sq_le_sqrt {t : ℝ} (ht : 1 ≤ t) : Real.log t ^ 2 ≤ 16 * Real.sqrt t := by
  have h0 : 0 ≤ t := by linarith
  set u := Real.sqrt (Real.sqrt t) with hudef
  have h1 : (1 : ℝ) ≤ Real.sqrt t := by
    have := Real.sqrt_le_sqrt ht; rwa [Real.sqrt_one] at this
  have h2 : (1 : ℝ) ≤ u := by
    have := Real.sqrt_le_sqrt h1; rwa [Real.sqrt_one] at this
  have hlog : Real.log t = 4 * Real.log u := by
    rw [hudef, Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt h0]; ring
  have hlu : Real.log u ≤ u := le_trans (Real.log_le_sub_one_of_pos (by linarith)) (by linarith)
  have hlu0 : 0 ≤ Real.log u := Real.log_nonneg h2
  have huu : u ^ 2 = Real.sqrt t := Real.sq_sqrt (Real.sqrt_nonneg _)
  rw [hlog]
  calc (4 * Real.log u) ^ 2 = 16 * Real.log u ^ 2 := by ring
    _ ≤ 16 * u ^ 2 := by gcongr
    _ = 16 * Real.sqrt t := by rw [huu]

/-- **Corollary 5.5.** If `d_p ≤ √p / (log p)^2` for all elite primes `p ≥ p₀`, then
`E(N) ≪ N / (log N)^2`; explicitly, `E(N) ≤ 192 N / (log N)^2` for all large `N`. -/
theorem cor_oddpart {p₀ : ℕ}
    (h : ∀ p, IsElite p → p₀ ≤ p → (dv p : ℝ) ≤ Real.sqrt p / Real.log p ^ 2) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (E N : ℝ) ≤ 192 * N / Real.log N ^ 2 := by
  classical
  refine ⟨(p₀ + 1) ^ 2 + 2, fun N hN => ?_⟩
  have hN2' : 2 ≤ N := le_trans (Nat.le_add_left 2 _) hN
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2'
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set L := Real.log N with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  set s := Real.sqrt N with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hss : s * s = N := Real.mul_self_sqrt hN0
  have hp₀s : (p₀ : ℝ) + 1 ≤ s := by
    have h1 : (((p₀ + 1) ^ 2 : ℕ) : ℝ) ≤ N := by
      exact_mod_cast le_trans (Nat.le_add_right _ 2) hN
    push_cast at h1
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at h2
  -- `J` with `√N / 2 < 2^J ≤ √N`
  set J := Nat.log 2 (Nat.sqrt N) with hJdef
  have hsqrt0 : Nat.sqrt N ≠ 0 := by
    have : 1 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by omega)
    omega
  have hJ1 : (2 : ℝ) ^ J ≤ s := by
    have h1 : 2 ^ J ≤ Nat.sqrt N := Nat.pow_log_le_self 2 hsqrt0
    have h2 : ((2 ^ J : ℕ) : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact le_trans h2 Real.nat_sqrt_le_real_sqrt
  have hJ2 : s < 2 * 2 ^ J := by
    have h1 : Nat.sqrt N < 2 ^ (J + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 : Nat.sqrt N + 1 ≤ 2 * 2 ^ J := by rw [pow_succ] at h1; omega
    have h3 : ((Nat.sqrt N : ℕ) : ℝ) + 1 ≤ 2 * 2 ^ J := by exact_mod_cast h2
    linarith [Real.real_sqrt_lt_nat_sqrt_succ (a := N)]
  -- dyadic points `z j = N / 2^j`
  set z : ℕ → ℝ := fun j => (N : ℝ) / 2 ^ j with hzdef
  have hz0 : ∀ j, 0 ≤ z j := fun j => by simp only [hzdef]; positivity
  have hzj : ∀ j, z j = N * (1 / 2) ^ j := fun j => by
    simp only [hzdef]; rw [one_div, inv_pow, div_eq_mul_inv]
  have hzJ : z J ≤ 2 * s := by
    simp only [hzdef]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hzJs : s ≤ z J := by
    simp only [hzdef]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hzmono : ∀ j, j + 1 ≤ J → z J ≤ z (j + 1) := by
    intro j hj
    simp only [hzdef]
    exact div_le_div_of_nonneg_left hN0 (by positivity) (pow_le_pow_right₀ (by norm_num) hj)
  -- the decomposition
  let A := (eliteSet N).filter (fun p : ℕ => p < p₀)
  let B := (eliteSet N).filter (fun p : ℕ => (p : ℝ) ≤ z J)
  let C : ℕ → Finset ℕ := fun j =>
    (eliteSet N).filter (fun p : ℕ => p₀ ≤ p ∧ z (j + 1) < p ∧ (p : ℝ) ≤ z j)
  have hcover : eliteSet N ⊆ A ∪ B ∪ (range J).biUnion C := by
    intro p hp
    have hpN : p ≤ N := (mem_eliteSet.mp hp).1
    by_cases h1 : p < p₀
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hp, h1⟩))
    by_cases h2 : (p : ℝ) ≤ z J
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hp, h2⟩))
    apply mem_union_right
    rw [mem_biUnion]
    have claim : ∀ j, j ≤ J → (p : ℝ) ≤ z j ∨ ∃ i < j, z (i + 1) < p ∧ (p : ℝ) ≤ z i := by
      intro j
      induction j with
      | zero =>
        intro _
        left
        simp only [hzdef, pow_zero, div_one]
        exact_mod_cast hpN
      | succ j ih =>
        intro hj
        rcases ih (by omega) with h3 | ⟨i, hi, h3⟩
        · by_cases h4 : (p : ℝ) ≤ z (j + 1)
          · left; exact h4
          · right; exact ⟨j, by omega, lt_of_not_ge h4, h3⟩
        · right; exact ⟨i, by omega, h3⟩
    rcases claim J le_rfl with h3 | ⟨i, hi, h3, h4⟩
    · exact absurd h3 h2
    · exact ⟨i, mem_range.mpr hi, mem_filter.mpr ⟨hp, not_lt.mp h1, h3, h4⟩⟩
  -- the small primes
  have hA : (A.card : ℝ) ≤ p₀ := by
    have hsub : A ⊆ range p₀ := fun p hp => mem_range.mpr (mem_filter.mp hp).2
    have h1 := card_le_card hsub
    rw [card_range] at h1
    exact_mod_cast h1
  have hB : (B.card : ℝ) ≤ 2 * s + 1 := by
    have hsub : B ⊆ range (⌊z J⌋₊ + 1) := fun p hp =>
      mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (mem_filter.mp hp).2))
    have h1 := card_le_card hsub
    rw [card_range] at h1
    have h2 : (B.card : ℝ) ≤ (⌊z J⌋₊ : ℝ) + 1 := by exact_mod_cast h1
    linarith [Nat.floor_le (hz0 J)]
  -- one dyadic range, by Lemma 5.4
  have hC : ∀ j ∈ range J, ((C j).card : ℝ) ≤ 8 * z j / L ^ 2 + 2 * Real.sqrt (z j) := by
    intro j hj
    have hjJ : j + 1 ≤ J := mem_range.mp hj
    set y : ℝ := 4 * Real.sqrt (z j) / L ^ 2 with hy
    have hy0 : 0 ≤ y := by positivity
    have hsub : C j ⊆
        (range (⌊z j⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ (dv p : ℝ) ≤ y) := by
      intro p hp
      obtain ⟨hpS, hp0, hlow, hhigh⟩ := mem_filter.mp hp
      have hpe : IsElite p := (mem_eliteSet.mp hpS).2
      refine mem_filter.mpr
        ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hhigh)), hpe.1, hpe.2.1, ?_⟩
      have hps : s < (p : ℝ) := lt_of_le_of_lt (le_trans hzJs (hzmono j hjJ)) hlow
      have hlogp : L / 2 ≤ Real.log p := by
        have : Real.log s = L / 2 := by rw [hsdef, Real.log_sqrt hN0]
        rw [← this]
        exact Real.log_le_log hs hps.le
      calc (dv p : ℝ) ≤ Real.sqrt p / Real.log p ^ 2 := h p hpe hp0
        _ ≤ Real.sqrt (z j) / (L / 2) ^ 2 := by gcongr
        _ = y := by rw [hy]; field_simp; ring
    have h1 : ((C j).card : ℝ) ≤
        (((range (⌊z j⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ (dv p : ℝ) ≤ y)).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    have h3 := le_trans h1 (card_dv_le (hz0 j) hy0)
    have h4 : Real.sqrt (z j) * Real.sqrt (z j) = z j := Real.mul_self_sqrt (hz0 j)
    calc ((C j).card : ℝ) ≤ 2 * (y + 1) * Real.sqrt (z j) := h3
      _ = 8 * (Real.sqrt (z j) * Real.sqrt (z j)) / L ^ 2 + 2 * Real.sqrt (z j) := by
          rw [hy]; field_simp; ring
      _ = 8 * z j / L ^ 2 + 2 * Real.sqrt (z j) := by rw [h4]
  -- summing over the dyadic ranges
  set w : ℝ := Real.sqrt (1 / 2) with hwdef
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw2 : w ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hw34 : w ≤ 3 / 4 := by
    have h1 := Real.sqrt_le_sqrt (show (1 / 2 : ℝ) ≤ (3 / 4) ^ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h1
  have hsqz : ∀ j, Real.sqrt (z j) = s * w ^ j := by
    intro j
    rw [← Real.sqrt_sq (by positivity : 0 ≤ s * w ^ j)]
    congr 1
    rw [hzj, mul_pow, ← pow_mul, mul_comm j 2, pow_mul, hw2, sq, hss]
  have hgeom1 : ∑ j ∈ range J, ((1 : ℝ) / 2) ^ j ≤ 2 := sum_geometric_two_le J
  have hgeom2 : ∑ j ∈ range J, w ^ j ≤ 4 := by
    have h1 := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hw0 (by linarith)
    rw [← range_eq_Ico, pow_zero] at h1
    have h2 : 1 / (1 - w) ≤ 4 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have hCsum : ∑ j ∈ range J, ((C j).card : ℝ) ≤ 16 * N / L ^ 2 + 8 * s := by
    calc ∑ j ∈ range J, ((C j).card : ℝ)
        ≤ ∑ j ∈ range J, (8 * z j / L ^ 2 + 2 * Real.sqrt (z j)) := sum_le_sum hC
      _ = 8 * N / L ^ 2 * ∑ j ∈ range J, ((1 : ℝ) / 2) ^ j + 2 * s * ∑ j ∈ range J, w ^ j := by
          rw [sum_add_distrib, mul_sum, mul_sum]
          congr 1 <;> apply sum_congr rfl <;> intro j _
          · rw [hzj]; ring
          · rw [hsqz]; ring
      _ ≤ 8 * N / L ^ 2 * 2 + 2 * s * 4 := by gcongr
      _ = 16 * N / L ^ 2 + 8 * s := by ring
  -- `√N ≤ 16 N / (log N)^2`
  have hlogs : L ^ 2 ≤ 16 * s := log_sq_le_sqrt (by linarith)
  have hsL : s ≤ 16 * N / L ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hE : (E N : ℝ) ≤ A.card + B.card + ∑ j ∈ range J, ((C j).card : ℝ) := by
    have h1 := (card_le_card hcover).trans
      ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
    have h2 := card_union_le A B
    have h3 : E N ≤ A.card + B.card + ∑ j ∈ range J, (C j).card := by
      unfold E; omega
    exact_mod_cast h3
  calc (E N : ℝ) ≤ A.card + B.card + ∑ j ∈ range J, ((C j).card : ℝ) := hE
    _ ≤ p₀ + (2 * s + 1) + (16 * N / L ^ 2 + 8 * s) := by linarith
    _ ≤ 11 * s + 16 * N / L ^ 2 := by linarith
    _ ≤ 11 * (16 * N / L ^ 2) + 16 * N / L ^ 2 := by linarith
    _ = 192 * N / L ^ 2 := by ring

end ElitePrimes
