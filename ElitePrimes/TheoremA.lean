import ElitePrimes.Periodicity
import ElitePrimes.Count

/-!
# Proposition 3.1 and inequality (2) at integers, from the Brun–Titchmarsh inequality

`BrunTitchmarsh` is an explicit ASSUMPTION (it is not in Mathlib). Everything else is proved.

`theoremA`: if `T ≥ 1` and `(2^T * 2^(2^T))^2 ≤ N`, then
  `E(N) * (2^T * log N) ≤ 4 (T + 1) N`.
The versions for real `x` and the asymptotic form of Theorem 1.1 (the choice of `T`) are in
`RealBounds.lean`.
-/

namespace ElitePrimes

open Nat Finset

/-- Number of primes `p ≤ N` with `p ≡ a (mod q)`. -/
def primesInAP (N q a : ℕ) : ℕ :=
  ((range (N + 1)).filter (fun p => p.Prime ∧ p % q = a % q)).card

/-- Brun–Titchmarsh (Montgomery–Vaughan 1973), multiplied out:
`π(N; q, a) ≤ 2N / (φ(q) log(N/q))` for `1 ≤ q < N`, `gcd(a, q) = 1`. -/
def BrunTitchmarsh : Prop :=
  ∀ N q a : ℕ, 1 ≤ q → q < N → Nat.Coprime a q →
    (primesInAP N q a : ℝ) * ((Nat.totient q : ℝ) * Real.log ((N : ℝ) / q)) ≤ 2 * N

open Classical in
/-- The elite primes `p ≤ N`. -/
noncomputable def eliteSet (N : ℕ) : Finset ℕ := (range (N + 1)).filter IsElite

/-- `E(N)`, the number of elite primes `≤ N`. -/
noncomputable def E (N : ℕ) : ℕ := (eliteSet N).card

theorem log_half_le {N m : ℕ} (hm : 0 < m) (hmN : m ^ 2 ≤ N) :
    (1 / 2) * Real.log N ≤ Real.log ((N : ℝ) / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN : 0 < N := lt_of_lt_of_le (pow_pos hm 2) hmN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.log_div hN'.ne' hm'.ne']
  have hsq : Real.log ((m : ℝ) ^ 2) = 2 * Real.log m := by
    rw [Real.log_pow]; norm_num
  have h2 : 2 * Real.log m ≤ Real.log N := by
    rw [← hsq]
    exact Real.log_le_log (pow_pos hm' 2) (by exact_mod_cast hmN)
  linarith

/-- The block `e_p = e` with `1 ≤ e < T`: at most `4N / (2^T log N)` elite primes. -/
theorem block_bound (hBT : BrunTitchmarsh) {N T e : ℕ} (he1 : 1 ≤ e) (heT : e < T)
    (hN : (2 ^ T * 2 ^ (2 ^ T)) ^ 2 ≤ N) :
    (((eliteSet N).filter (fun p => ev p = e)).card : ℝ) * (2 ^ T * Real.log N) ≤ 4 * N := by
  classical
  set Se := (eliteSet N).filter (fun p => ev p = e) with hSe
  have hSe_mem : ∀ p ∈ Se, p ≤ N ∧ IsElite p ∧ ev p = e := by
    intro p hp
    simp only [hSe, eliteSet, mem_filter, mem_range] at hp
    exact ⟨Nat.lt_succ_iff.mp hp.1.1, hp.1.2, hp.2⟩
  -- elite primes with e_p = e are units mod Me e T
  have hcop : ∀ p ∈ Se, Nat.Coprime p (Me e T) := by
    intro p hp
    obtain ⟨-, hpe, hev⟩ := hSe_mem p hp
    show Nat.Coprime p (2 ^ (e + 1) * Pe e T)
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      intro h2
      exact hpe.2.1 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpe.1).mp h2).symm
    · apply Nat.Coprime.prod_right
      intro n hn
      have hJ : jacobiSym p (F n) = -1 :=
        elite_jacobi_p_F hpe (by rw [hev]; exact (mem_Ico.mp hn).1)
      haveI : NeZero (F n) := ⟨(F_pos n).ne'⟩
      have hg : Int.gcd (p : ℤ) (F n) = 1 := by
        by_contra hne
        have h0 := (jacobiSym.eq_zero_iff_not_coprime).mpr hne
        rw [hJ] at h0
        norm_num at h0
      rwa [Int.gcd_natCast_natCast] at hg
  let f : ℕ → (ZMod (Me e T))ˣ := fun p =>
    if h : Nat.Coprime p (Me e T) then ZMod.unitOfCoprime p h else 1
  have hf_val : ∀ p ∈ Se, ((f p : (ZMod (Me e T))ˣ) : ZMod (Me e T)).val = p % Me e T := by
    intro p hp
    simp only [f]
    rw [dif_pos (hcop p hp), ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  -- each such prime lands in R_e (Lemma 2.2)
  have hmapsto : ∀ p ∈ Se, f p ∈ Rset e T := by
    intro p hp
    obtain ⟨-, hpe, hev⟩ := hSe_mem p hp
    simp only [Rset, mem_filter, mem_univ, true_and, sig, Prod.mk.injEq]
    rw [hf_val p hp]
    constructor
    · rw [Nat.mod_mod_of_dvd _ (two_pow_dvd_Me e T), ← hev]
      exact mod_pow_ev hpe.1 hpe.2.1
    · apply Finset.filter_true_of_mem
      intro n hn
      rw [jacobi_congr ((Nat.mod_modEq p (Me e T)).of_dvd (F_dvd_Me hn))]
      exact elite_jacobi_p_F hpe (by rw [hev]; exact (mem_Ico.mp hn).1)
  -- each residue class contributes at most π(N; M, u)
  have hfiber : ∀ u ∈ Rset e T,
      (Se.filter (fun p => f p = u)).card ≤ primesInAP N (Me e T) (u : ZMod (Me e T)).val := by
    intro u _
    apply card_le_card
    intro p hp
    rw [mem_filter] at hp
    obtain ⟨hpS, hpu⟩ := hp
    obtain ⟨hpN, hpe, -⟩ := hSe_mem p hpS
    simp only [mem_filter, mem_range]
    refine ⟨by omega, hpe.1, ?_⟩
    rw [← hf_val p hpS, hpu, Nat.mod_eq_of_lt (ZMod.val_lt _)]
  have hcard : Se.card ≤ ∑ u ∈ Rset e T, primesInAP N (Me e T) (u : ZMod (Me e T)).val := by
    rw [card_eq_sum_card_fiberwise hmapsto]
    exact sum_le_sum hfiber
  -- sizes: M ≤ 2^T 2^(2^T), M^2 ≤ N, M < N
  have hMle : Me e T ≤ 2 ^ T * 2 ^ (2 ^ T) :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) heT) (prod_F_Ico_lt e T).le
  have h4 : 2 ≤ Me e T :=
    calc 2 ≤ 2 ^ (e + 1) := Nat.le_self_pow (by omega) 2
      _ ≤ 2 ^ (e + 1) * Pe e T := Nat.le_mul_of_pos_right _ (Pe_pos e T)
  have hMsq : (Me e T) ^ 2 ≤ N := le_trans (Nat.pow_le_pow_left hMle 2) hN
  have hMN : Me e T < N := by nlinarith
  have hhalf := log_half_le (Me_pos e T) hMsq
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by nlinarith : 1 < N)
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hL : 0 < Real.log ((N : ℝ) / Me e T) := by linarith
  have hφpos : (0 : ℝ) < Nat.totient (Me e T) := by
    exact_mod_cast Nat.totient_pos.mpr (Me_pos e T)
  -- Brun–Titchmarsh in every admissible class
  have hBTu : ∀ u ∈ Rset e T, (primesInAP N (Me e T) (u : ZMod (Me e T)).val : ℝ) *
      ((Nat.totient (Me e T) : ℝ) * Real.log ((N : ℝ) / Me e T)) ≤ 2 * N :=
    fun u _ => hBT N (Me e T) _ (Me_pos e T) hMN (ZMod.val_coe_unit_coprime u)
  have hsum : (Se.card : ℝ) * ((Nat.totient (Me e T) : ℝ) * Real.log ((N : ℝ) / Me e T)) ≤
      ((Rset e T).card : ℝ) * (2 * N) := by
    have h1 : (Se.card : ℝ) ≤
        ∑ u ∈ Rset e T, (primesInAP N (Me e T) (u : ZMod (Me e T)).val : ℝ) := by
      exact_mod_cast hcard
    calc (Se.card : ℝ) * ((Nat.totient (Me e T) : ℝ) * Real.log ((N : ℝ) / Me e T))
        ≤ (∑ u ∈ Rset e T, (primesInAP N (Me e T) (u : ZMod (Me e T)).val : ℝ)) *
            ((Nat.totient (Me e T) : ℝ) * Real.log ((N : ℝ) / Me e T)) :=
          mul_le_mul_of_nonneg_right h1 (mul_pos hφpos hL).le
      _ = ∑ u ∈ Rset e T, (primesInAP N (Me e T) (u : ZMod (Me e T)).val : ℝ) *
            ((Nat.totient (Me e T) : ℝ) * Real.log ((N : ℝ) / Me e T)) := by
          rw [sum_mul]
      _ ≤ ∑ u ∈ Rset e T, (2 * N : ℝ) := sum_le_sum hBTu
      _ = ((Rset e T).card : ℝ) * (2 * N) := by rw [sum_const, nsmul_eq_mul]
  -- Lemma 2.3: |R_e| * 2^T = φ(M)
  have hRT : ((Rset e T).card : ℝ) * 2 ^ T = Nat.totient (Me e T) := by
    exact_mod_cast card_R_mul he1 heT.le
  have key : (Se.card : ℝ) * Real.log ((N : ℝ) / Me e T) * 2 ^ T ≤ 2 * N := by
    have h2 : (Se.card : ℝ) * Real.log ((N : ℝ) / Me e T) * 2 ^ T * Nat.totient (Me e T)
        ≤ 2 * N * Nat.totient (Me e T) := by
      calc (Se.card : ℝ) * Real.log ((N : ℝ) / Me e T) * 2 ^ T * Nat.totient (Me e T)
          = (Se.card : ℝ) * ((Nat.totient (Me e T) : ℝ) * Real.log ((N : ℝ) / Me e T)) * 2 ^ T := by
            ring
        _ ≤ ((Rset e T).card : ℝ) * (2 * N) * 2 ^ T :=
            mul_le_mul_of_nonneg_right hsum (by positivity)
        _ = 2 * N * (((Rset e T).card : ℝ) * 2 ^ T) := by ring
        _ = 2 * N * Nat.totient (Me e T) := by rw [hRT]
    exact le_of_mul_le_mul_right h2 hφpos
  have hSe0 : (0 : ℝ) ≤ Se.card := Nat.cast_nonneg _
  have h3 : (Se.card : ℝ) * ((1 / 2) * Real.log N) ≤
      (Se.card : ℝ) * Real.log ((N : ℝ) / Me e T) :=
    mul_le_mul_of_nonneg_left hhalf hSe0
  have h5 := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 2 ^ T)
  calc (Se.card : ℝ) * (2 ^ T * Real.log N)
      = 2 * ((Se.card : ℝ) * ((1 / 2) * Real.log N) * 2 ^ T) := by ring
    _ ≤ 2 * ((Se.card : ℝ) * Real.log ((N : ℝ) / Me e T) * 2 ^ T) := by linarith
    _ ≤ 2 * (2 * N) := by linarith [key]
    _ = 4 * N := by ring

/-- The block `e_p ≥ T`: at most `8N / (2^T log N)` elite primes. -/
theorem big_block_bound (hBT : BrunTitchmarsh) {N T : ℕ} (hT : 1 ≤ T)
    (hN : (2 ^ T * 2 ^ (2 ^ T)) ^ 2 ≤ N) :
    (((eliteSet N).filter (fun p => T ≤ ev p)).card : ℝ) * (2 ^ T * Real.log N) ≤ 8 * N := by
  classical
  set Sb := (eliteSet N).filter (fun p => T ≤ ev p) with hSb
  have hsub : Sb.card ≤ primesInAP N (2 ^ T) 1 := by
    apply card_le_card
    intro p hp
    simp only [hSb, eliteSet, mem_filter, mem_range] at hp
    obtain ⟨⟨hpN, hpe⟩, hTe⟩ := hp
    simp only [mem_filter, mem_range]
    exact ⟨hpN, hpe.1, mod_pow_of_le_ev hpe.1 hTe⟩
  have hQ : 2 ^ T ≤ 2 ^ T * 2 ^ (2 ^ T) := Nat.le_mul_of_pos_right _ (by positivity)
  have hsq : (2 ^ T) ^ 2 ≤ N := le_trans (Nat.pow_le_pow_left hQ 2) hN
  have h2T : 2 ≤ 2 ^ T := Nat.le_self_pow (by omega) 2
  have hqN : 2 ^ T < N := by nlinarith
  have hhalf := log_half_le (by positivity : 0 < 2 ^ T) hsq
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hφ : (Nat.totient (2 ^ T) : ℝ) = 2 ^ (T - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
    push_cast
    ring
  have hBT1 := hBT N (2 ^ T) 1 Nat.one_le_two_pow hqN (Nat.coprime_one_left _)
  rw [hφ] at hBT1
  have h2pow : (2 : ℝ) ^ T = 2 * 2 ^ (T - 1) := by
    have hT' : T = (T - 1) + 1 := by omega
    conv_lhs => rw [hT']
    rw [pow_succ]; ring
  have hcardR : (Sb.card : ℝ) ≤ primesInAP N (2 ^ T) 1 := by exact_mod_cast hsub
  have hπ0 : (0 : ℝ) ≤ primesInAP N (2 ^ T) 1 := Nat.cast_nonneg _
  have hpos : (0 : ℝ) < 2 ^ (T - 1) := by positivity
  have h1 : (Sb.card : ℝ) * (2 ^ (T - 1) * ((1 / 2) * Real.log N)) ≤
      (primesInAP N (2 ^ T) 1 : ℝ) * (2 ^ (T - 1) * Real.log ((N : ℝ) / (2 ^ T : ℕ))) := by
    refine mul_le_mul hcardR (mul_le_mul_of_nonneg_left hhalf hpos.le) ?_ hπ0
    exact (mul_pos hpos (by linarith)).le
  calc (Sb.card : ℝ) * (2 ^ T * Real.log N)
      = 4 * ((Sb.card : ℝ) * (2 ^ (T - 1) * ((1 / 2) * Real.log N))) := by
        rw [h2pow]; ring
    _ ≤ 4 * (2 * N) := by linarith [h1, hBT1]
    _ = 8 * N := by ring

/-- **Inequality (2)** at integers (Proposition 3.1). Assuming Brun–Titchmarsh, for `T ≥ 1` and
`(2^T * 2^(2^T))^2 ≤ N`: `E(N) * 2^T * log N ≤ 4 (T + 1) N`. -/
theorem theoremA (hBT : BrunTitchmarsh) (N T : ℕ) (hT : 1 ≤ T)
    (hN : (2 ^ T * 2 ^ (2 ^ T)) ^ 2 ≤ N) :
    (E N : ℝ) * (2 ^ T * Real.log N) ≤ 4 * (T + 1) * N := by
  classical
  have hsub : eliteSet N ⊆
      ((Ico 1 T).biUnion (fun e => (eliteSet N).filter (fun p => ev p = e))) ∪
        (eliteSet N).filter (fun p => T ≤ ev p) := by
    intro p hp
    have hpe : IsElite p := (mem_filter.mp hp).2
    have h1 := one_le_ev hpe.1 hpe.2.1
    by_cases hlt : ev p < T
    · apply mem_union_left
      rw [mem_biUnion]
      exact ⟨ev p, mem_Ico.mpr ⟨h1, hlt⟩, mem_filter.mpr ⟨hp, rfl⟩⟩
    · apply mem_union_right
      exact mem_filter.mpr ⟨hp, not_lt.mp hlt⟩
  have hcardle : E N ≤ ∑ e ∈ Ico 1 T, ((eliteSet N).filter (fun p => ev p = e)).card +
      ((eliteSet N).filter (fun p => T ≤ ev p)).card :=
    (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_right card_biUnion_le _))
  have hN1 : 1 ≤ N := le_trans (Nat.one_le_pow _ _ (by positivity)) hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hpos : (0 : ℝ) ≤ 2 ^ T * Real.log N := mul_nonneg (by positivity) hlog
  calc (E N : ℝ) * (2 ^ T * Real.log N)
      ≤ ((∑ e ∈ Ico 1 T, (((eliteSet N).filter (fun p => ev p = e)).card : ℝ)) +
          (((eliteSet N).filter (fun p => T ≤ ev p)).card : ℝ)) * (2 ^ T * Real.log N) := by
        apply mul_le_mul_of_nonneg_right _ hpos
        exact_mod_cast hcardle
    _ = ∑ e ∈ Ico 1 T, (((eliteSet N).filter (fun p => ev p = e)).card : ℝ) *
            (2 ^ T * Real.log N) +
          (((eliteSet N).filter (fun p => T ≤ ev p)).card : ℝ) * (2 ^ T * Real.log N) := by
        rw [add_mul, sum_mul]
    _ ≤ ∑ e ∈ Ico 1 T, (4 * N : ℝ) + 8 * N := by
        apply _root_.add_le_add
        · apply sum_le_sum
          intro e he
          rw [mem_Ico] at he
          exact block_bound hBT he.1 he.2 hN
        · exact big_block_bound hBT hT hN
    _ = 4 * (T + 1) * N := by
        rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hT]
        push_cast
        ring

end ElitePrimes
