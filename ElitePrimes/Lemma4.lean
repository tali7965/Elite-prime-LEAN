import ElitePrimes.Periodicity

/-!
# Lemma 5.4: the counting step

* `card_ord_eq_lt`      : fewer than `D` odd primes have `ord_p(2) = D`.
* `card_ord_eq_le_div`  : at most `N / D` of them are `≤ N`.
* `card_dv_eq_le`       : `#{p ≤ N : d_p = d} ≤ ∑_{s ≤ N} min(2^s d, N / (2^s d))`.

The final geometric-series estimate `∑_s min(2^s d, N/(2^s d)) ≤ 4 √N` and the sum over
odd `d ≤ y` are in `OddPart.lean`.
-/

namespace ElitePrimes

open Nat Finset

theorem card_ord_eq_lt (N D : ℕ) (hD : 0 < D) :
    ((range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ ord p = D)).card < D := by
  classical
  set S := (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ ord p = D) with hS
  have hmem : ∀ p ∈ S, p.Prime ∧ p ≠ 2 ∧ ord p = D := fun p hp => (mem_filter.mp hp).2
  -- every such p divides 2^D - 1
  have hdvd : ∀ p ∈ S, p ∣ 2 ^ D - 1 := by
    intro p hp
    obtain ⟨hpp, hp2, hord⟩ := hmem p hp
    haveI := Fact.mk hpp
    have h1 : (2 : ZMod p) ^ D = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    have h2 : ((2 ^ D - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      rw [h1]
      ring
    exact (CharP.cast_eq_zero_iff (ZMod p) p _).mp h2
  -- every such p is ≥ D + 1 (it is ≡ 1 mod D)
  have hge : ∀ p ∈ S, D + 1 ≤ p := by
    intro p hp
    obtain ⟨hpp, hp2, hord⟩ := hmem p hp
    haveI := Fact.mk hpp
    have h1 : D ∣ p - 1 := hord ▸ ord_dvd hp2
    have h2 : 0 < p - 1 := by have := hpp.two_le; omega
    have h3 := Nat.le_of_dvd h2 h1
    omega
  have hprod : (∏ p ∈ S, p) ∣ 2 ^ D - 1 :=
    Finset.prod_primes_dvd _ (fun p hp => (hmem p hp).1.prime) hdvd
  have hpos : 0 < 2 ^ D - 1 := by
    have : 2 ≤ 2 ^ D := Nat.le_self_pow hD.ne' 2
    omega
  have hle : ∏ p ∈ S, p ≤ 2 ^ D - 1 := Nat.le_of_dvd hpos hprod
  have hlow : (D + 1) ^ S.card ≤ ∏ p ∈ S, p := Finset.pow_card_le_prod _ _ _ hge
  have hup : 2 ^ D ≤ (D + 1) ^ D := Nat.pow_le_pow_left (by omega) D
  by_contra hcon
  push_neg at hcon
  have h4 : (D + 1) ^ D ≤ (D + 1) ^ S.card := Nat.pow_le_pow_right (by omega) hcon
  omega

theorem card_ord_eq_le_div (N D : ℕ) (hD : 0 < D) :
    ((range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ ord p = D)).card ≤ N / D := by
  classical
  have h : ((range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ ord p = D)).card ≤
      (Icc 1 (N / D)).card := by
    apply card_le_card_of_injOn (fun p => (p - 1) / D)
    · intro p hp
      simp only [mem_coe, mem_filter, mem_range] at hp
      obtain ⟨hpN, hpp, hp2, hord⟩ := hp
      haveI := Fact.mk hpp
      have h1 : D ∣ p - 1 := hord ▸ ord_dvd hp2
      have h2 : 0 < p - 1 := by have := hpp.two_le; omega
      have h3 := Nat.le_of_dvd h2 h1
      simp only [mem_coe, mem_Icc]
      constructor
      · exact (Nat.le_div_iff_mul_le hD).mpr (by omega)
      · exact Nat.div_le_div_right (by omega)
    · intro p hp q hq hpq
      simp only [mem_coe, mem_filter, mem_range] at hp hq
      obtain ⟨-, hpp, hp2, hord⟩ := hp
      obtain ⟨-, hqp, hq2, hordq⟩ := hq
      have h1 : D ∣ p - 1 := by haveI := Fact.mk hpp; exact hord ▸ ord_dvd hp2
      have h1' : D ∣ q - 1 := by haveI := Fact.mk hqp; exact hordq ▸ ord_dvd hq2
      have hpq' : (p - 1) / D = (q - 1) / D := hpq
      have e1 := Nat.div_mul_cancel h1
      have e2 := Nat.div_mul_cancel h1'
      have h5 : p - 1 = q - 1 := by rw [← e1, ← e2, hpq']
      have := hpp.two_le
      have := hqp.two_le
      omega
  simpa using h

/-- For fixed odd part `d`, the odd primes `p ≤ N` with `d_p = d` number at most
`∑_{s ≤ N} min(2^s d, N / (2^s d))`. -/
theorem card_dv_eq_le (N d : ℕ) (hd : 0 < d) :
    ((range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ dv p = d)).card ≤
      ∑ s ∈ range (N + 1), min (2 ^ s * d) (N / (2 ^ s * d)) := by
  classical
  have hsub : (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ dv p = d) ⊆
      (range (N + 1)).biUnion (fun s =>
        (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ ord p = 2 ^ s * d)) := by
    intro p hp
    simp only [mem_filter, mem_range] at hp
    obtain ⟨hpN, hpp, hp2, hdv⟩ := hp
    haveI := Fact.mk hpp
    rw [mem_biUnion]
    refine ⟨sv p, ?_, ?_⟩
    · have h1 : 2 ^ sv p ≤ ord p := Nat.le_of_dvd (ord_pos hp2) pow_padicValNat_dvd
      have h2 : ord p ≤ p - 1 := Nat.le_of_dvd (by have := hpp.two_le; omega) (ord_dvd hp2)
      -- `Nat.lt_two_pow_self : n < 2 ^ n` (implicit `n` in current Mathlib)
      have h3 : sv p < 2 ^ sv p := Nat.lt_two_pow_self
      rw [mem_range]
      omega
    · simp only [mem_filter, mem_range]
      exact ⟨hpN, hpp, hp2, by rw [ord_eq p, hdv]⟩
  calc ((range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ dv p = d)).card
      ≤ ((range (N + 1)).biUnion (fun s =>
          (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ ord p = 2 ^ s * d))).card :=
        card_le_card hsub
    _ ≤ ∑ s ∈ range (N + 1),
          ((range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ ord p = 2 ^ s * d)).card :=
        card_biUnion_le
    _ ≤ ∑ s ∈ range (N + 1), min (2 ^ s * d) (N / (2 ^ s * d)) := by
        apply sum_le_sum
        intro s _
        have hpos : 0 < 2 ^ s * d := Nat.mul_pos (by positivity) hd
        exact le_min (card_ord_eq_lt N _ hpos).le (card_ord_eq_le_div N _ hpos)

end ElitePrimes
