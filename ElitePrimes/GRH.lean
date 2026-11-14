import ElitePrimes.Characters
import ElitePrimes.Structure
import ElitePrimes.OddPart

/-!
# Section 4: the bound under GRH (Theorem 1.2)

Lemma 4.1 is a consequence of GRH whose proof needs the explicit formula, which is not in
mathlib. It is an explicit ASSUMPTION here (`GRHCharSum`), in the same way as
`BrunTitchmarsh`. Everything else is proved.

* `GRHCharSum`        : Lemma 4.1 (assumed).
* `grh_block_bound`   : the bound for `N_e` in the proof of Theorem 1.2.
* `grh_big_block`     : the primes with `e_p ≥ T`.
* `theoremB_explicit` : `E(N) ≤ 8(T+1)N/(3 · 2^T log N) + T c₀ √N (2^(T+1) + log N)`.
* `theoremB`          : **Theorem 1.2**, `E(N) ≪ N^(3/4) (log N)^(1/2)`.
-/

namespace ElitePrimes

open Nat Finset

/-- Lemma 4.1 with constant `c₀`: for every `q ≥ 1`, every non-principal character `χ mod q`
and every real `x ≥ 2`, `‖∑_{p ≤ x} χ(p)‖ ≤ c₀ √x log(qx)`. -/
def GRHCharSumWith (c₀ : ℝ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ x : ℝ, 2 ≤ x →
    ‖∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, χ (p : ZMod q)‖ ≤
      c₀ * Real.sqrt x * Real.log (q * x)

/-- **Lemma 4.1** (a standard consequence of GRH; ASSUMED). -/
def GRHCharSum : Prop := ∃ c₀ : ℝ, 1 ≤ c₀ ∧ GRHCharSumWith c₀

/-- If `p ≡ 1 + 2^e (mod 2^(e+1))`, then `e_p = e`. -/
theorem ev_eq_of_mod {p e : ℕ} (h : p % 2 ^ (e + 1) = 1 + 2 ^ e) : ev p = e := by
  have h1 := Nat.mod_add_div p (2 ^ (e + 1))
  rw [h] at h1
  set k := p / 2 ^ (e + 1)
  have h2 : p = 2 ^ e * (1 + 2 * k) + 1 := by rw [← h1, pow_succ]; ring
  unfold ev
  rw [h2, Nat.add_sub_cancel, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by omega), add_zero]

/-- A prime `p ≡ 1 + 2^e (mod 2^(e+1))` is coprime to `M_e` (by (F2)). -/
theorem coprime_Me_of_mod {p e T : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (h : p % 2 ^ (e + 1) = 1 + 2 ^ e) : Nat.Coprime p (2 ^ (e + 1) * Pe e T) := by
  have hev := ev_eq_of_mod h
  apply Nat.Coprime.mul_right
  · apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h2
    have h3 : p % 2 = 0 := Nat.mod_eq_zero_of_dvd h2
    have h4 : p % 2 ^ (e + 1) % 2 = p % 2 := Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))
    rw [h] at h4
    have h5 : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
    omega
  · apply Nat.Coprime.prod_right
    intro n hn
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have h1 := ev_ge_of_dvd_F hp hdvd
    have h2 := (mem_Ico.mp hn).1
    omega

/-- `∏_{n ∈ I} (1 - j_n)/2 = 2^(-|I|) ∑_{B ⊆ I} (-1)^|B| ∏_{n ∈ B} j_n`. -/
theorem prod_half_expand {ι : Type*} [DecidableEq ι] (I : Finset ι) (j : ι → ℝ) :
    ∏ n ∈ I, (1 - j n) / 2 =
      (1 / 2) ^ I.card * ∑ B ∈ I.powerset, (-1) ^ B.card * ∏ n ∈ B, j n := by
  have h1 : ∏ n ∈ I, (1 - j n) / 2 = ∏ n ∈ I, ((1 / 2) * (-j n + 1)) :=
    prod_congr rfl (fun n _ => by ring)
  rw [h1, prod_mul_distrib, prod_const, prod_add]
  congr 1
  apply sum_congr rfl
  intro B _
  rw [prod_const_one, mul_one, prod_neg]

/-- `log (N / 2^k) ≥ (3/4) log N` when `(2^k)^4 ≤ N`. -/
theorem log_three_quarter {N k : ℕ} (hN : (2 ^ k) ^ 4 ≤ N) :
    (3 / 4) * Real.log N ≤ Real.log ((N : ℝ) / (2 ^ k : ℕ)) := by
  have hk : (0 : ℝ) < (2 ^ k : ℕ) := by positivity
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  rw [Real.log_div hN'.ne' hk.ne']
  have h4 : 4 * Real.log ((2 ^ k : ℕ) : ℝ) ≤ Real.log N := by
    have h5 : Real.log (((2 ^ k : ℕ) : ℝ) ^ 4) = 4 * Real.log ((2 ^ k : ℕ) : ℝ) := by
      rw [Real.log_pow]; norm_num
    rw [← h5]
    exact Real.log_le_log (pow_pos hk 4) (by exact_mod_cast hN)
  linarith

/-- The bound for `N_e = #{p ≤ N elite : e_p = e}` under Lemma 4.1 (proof of Theorem 1.2). -/
theorem grh_block_bound (hBT : BrunTitchmarsh) {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (hG : GRHCharSumWith c₀)
    {N T e : ℕ} (he1 : 1 ≤ e) (heT : e < T) (hN : (2 ^ T) ^ 4 ≤ N) :
    (((eliteSet N).filter (fun p => ev p = e)).card : ℝ) ≤
      8 * N / (3 * 2 ^ T * Real.log N) + c₀ * Real.sqrt N * (2 ^ (T + 1) + Real.log N) := by
  classical
  set q := 2 ^ (e + 1) with hq
  set I := Ico e T with hI
  -- sizes
  have h2T : 2 ≤ 2 ^ T := Nat.le_self_pow (by omega) 2
  have hqT : q ≤ 2 ^ T := Nat.pow_le_pow_right (by norm_num) heT
  have hqN : (q ^ 4 : ℕ) ≤ N := le_trans (Nat.pow_le_pow_left hqT 4) hN
  have hN16 : 16 ≤ N := le_trans (by nlinarith [Nat.pow_le_pow_left h2T 4]) hN
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have he2 : 2 ≤ 2 ^ e := Nat.le_self_pow (by omega) 2
  have hmod : (1 + 2 ^ e) % q = 1 + 2 ^ e :=
    Nat.mod_eq_of_lt (by rw [hq, pow_succ]; omega)
  set Pr := (range (N + 1)).filter Nat.Prime with hPr
  set C := (range (N + 1)).filter (fun p => p.Prime ∧ p % q = (1 + 2 ^ e) % q) with hC
  set j : ℕ → ℕ → ℝ := fun n p => ((jacobiSym p (F n) : ℤ) : ℝ) with hj
  set w : ℕ → ℝ := fun p => ∏ n ∈ I, (1 - j n p) / 2 with hw
  -- (1) the elite primes with `e_p = e` lie in `C` and have weight `1`
  set Se := (eliteSet N).filter (fun p => ev p = e) with hSe
  have hSeC : Se ⊆ C := by
    intro p hp
    obtain ⟨hpS, hev⟩ := mem_filter.mp hp
    obtain ⟨hpN, hpe⟩ := mem_eliteSet.mp hpS
    refine mem_filter.mpr ⟨mem_range.mpr (by omega), hpe.1, ?_⟩
    have h1 := mod_pow_ev hpe.1 hpe.2.1
    rw [hev] at h1
    rw [hmod]
    exact h1
  have hw1 : ∀ p ∈ Se, w p = 1 := by
    intro p hp
    obtain ⟨hpS, hev⟩ := mem_filter.mp hp
    have hpe := (mem_eliteSet.mp hpS).2
    apply prod_eq_one
    intro n hn
    have hJ : jacobiSym p (F n) = -1 := elite_jacobi_p_F hpe (by rw [hev]; exact (mem_Ico.mp hn).1)
    simp only [hj, hJ]
    norm_num
  have hw0 : ∀ p, 0 ≤ w p := by
    intro p
    apply prod_nonneg
    intro n _
    have h := jacobiSym.trichotomy (p : ℤ) (F n)
    simp only [hj]
    rcases h with h | h | h <;> rw [h] <;> norm_num
  have hcard : (Se.card : ℝ) ≤ ∑ p ∈ C, w p := by
    calc (Se.card : ℝ) = ∑ p ∈ Se, w p := by rw [sum_congr rfl hw1]; simp
      _ ≤ ∑ p ∈ C, w p := sum_le_sum_of_subset_of_nonneg hSeC (fun p _ _ => hw0 p)
  -- (2) expanding the product
  set S : Finset ℕ → ℝ := fun B => ∑ p ∈ C, ∏ n ∈ B, j n p with hS
  have hexp : ∑ p ∈ C, w p = (1 / 2) ^ I.card * ∑ B ∈ I.powerset, (-1) ^ B.card * S B := by
    have h1 : ∀ p, w p = (1 / 2) ^ I.card * ∑ B ∈ I.powerset, (-1) ^ B.card * ∏ n ∈ B, j n p :=
      fun p => prod_half_expand I (fun n => j n p)
    rw [sum_congr rfl (fun p _ => h1 p), ← mul_sum, sum_comm]
    congr 1
    apply sum_congr rfl
    intro B _
    rw [show S B = ∑ p ∈ C, ∏ n ∈ B, j n p from rfl, mul_sum]
  have hsplit : ∑ B ∈ I.powerset, (-1 : ℝ) ^ B.card * S B ≤
      S ∅ + ∑ B ∈ I.powerset.erase ∅, |S B| := by
    rw [← add_sum_erase _ _ (empty_mem_powerset I)]
    simp only [card_empty, pow_zero, one_mul]
    apply _root_.add_le_add le_rfl
    apply sum_le_sum
    intro B _
    calc (-1 : ℝ) ^ B.card * S B ≤ |(-1 : ℝ) ^ B.card * S B| := le_abs_self _
      _ = |S B| := by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  -- (3) Lemma 4.1 for every nonempty `B`
  set G := c₀ * Real.sqrt N * Real.log (((q * Pe e T : ℕ) : ℝ) * N) with hGdef
  have hSB : ∀ B ∈ I.powerset.erase ∅, |S B| ≤ G := by
    intro B hB
    have hBI : B ⊆ I := mem_powerset.mp (mem_of_mem_erase hB)
    have hBne : B.Nonempty := nonempty_iff_ne_empty.mpr (ne_of_mem_erase hB)
    haveI : NeZero (Pe e T) := ⟨(Pe_pos e T).ne'⟩
    haveI : NeZero q := ⟨by positivity⟩
    have hBM : ∀ n ∈ B, F n ∣ Pe e T := fun n hn => dvd_prod_of_mem F (hBI hn)
    have hQM : Nat.Coprime q (Pe e T) :=
      Nat.Coprime.prod_right (fun n _ => Nat.Coprime.pow_left _ (coprime_two_F n))
    set χ := jacChar B (q * Pe e T) (fun n hn => dvd_mul_of_dvd_right (hBM n hn) q) with hχ
    set a : ZMod q := ((1 + 2 ^ e : ℕ) : ZMod q) with ha_def
    have ha : IsUnit a := by
      rw [ha_def, ZMod.isUnit_iff_coprime]
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      have h5 : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
      omega
    have hCf : C = Pr.filter (fun p : ℕ => (p : ZMod q) = a) := by
      ext p
      simp only [hC, hPr, ha_def, mem_filter, ZMod.natCast_eq_natCast_iff', and_assoc]
    have hSC : ((S B : ℝ) : ℂ) = ∑ p ∈ C, χ (p : ZMod (q * Pe e T)) := by
      rw [show S B = ∑ p ∈ C, ∏ n ∈ B, j n p from rfl]
      push_cast
      apply sum_congr rfl
      intro p hp
      obtain ⟨-, hpp, hpq⟩ := mem_filter.mp hp
      rw [hχ, jacChar_natCast _ (coprime_Me_of_mod hpp he1 (hpq.trans hmod))]
      simp [hj]
    have horth := sum_filter_eq_char_sum ha Pr (fun p => χ (p : ZMod (q * Pe e T)))
    rw [← hCf] at horth
    have hψ : ∀ ψ : DirichletCharacter ℂ q,
        ‖∑ p ∈ Pr, ψ (p : ZMod q) * χ (p : ZMod (q * Pe e T))‖ ≤ G := by
      intro ψ
      have h1 : ∑ p ∈ Pr, ψ (p : ZMod q) * χ (p : ZMod (q * Pe e T)) =
          ∑ p ∈ Pr, (ψ.changeLevel (dvd_mul_right q (Pe e T)) * χ) (p : ZMod (q * Pe e T)) :=
        sum_congr rfl (fun p _ => (mul_jacChar_natCast _ ψ _ p).symm)
      rw [h1]
      have h2 := hG (q * Pe e T) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)) _
        (F3 hBne hBM hQM ψ) N hN2
      rw [Nat.floor_natCast] at h2
      exact h2
    have hG0 : 0 ≤ G := by
      rw [hGdef]
      apply mul_nonneg (mul_nonneg hc₀ (Real.sqrt_nonneg _))
      apply Real.log_nonneg
      have h1 : (1 : ℝ) ≤ ((q * Pe e T : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
      nlinarith
    have hnorm : ‖((S B : ℝ) : ℂ)‖ ≤ G := by
      rw [hSC, horth, norm_mul, norm_inv, Complex.norm_natCast]
      have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by positivity)
      calc (q.totient : ℝ)⁻¹ * ‖∑ ψ : DirichletCharacter ℂ q,
            ψ a⁻¹ * ∑ p ∈ Pr, ψ (p : ZMod q) * χ (p : ZMod (q * Pe e T))‖
          ≤ (q.totient : ℝ)⁻¹ * ∑ ψ : DirichletCharacter ℂ q, G := by
            gcongr
            refine (norm_sum_le _ _).trans (sum_le_sum fun ψ _ => ?_)
            rw [norm_mul]
            calc ‖ψ a⁻¹‖ * ‖∑ p ∈ Pr, ψ (p : ZMod q) * χ (p : ZMod (q * Pe e T))‖
                ≤ 1 * G := mul_le_mul (DirichletCharacter.norm_le_one ψ _) (hψ ψ)
                  (norm_nonneg _) zero_le_one
              _ = G := one_mul G
        _ = G := by
            rw [sum_const, card_dirichletCharacter, nsmul_eq_mul]
            field_simp
    rwa [Complex.norm_real, Real.norm_eq_abs] at hnorm
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    apply mul_nonneg (mul_nonneg hc₀ (Real.sqrt_nonneg _))
    apply Real.log_nonneg
    have h1 : (1 : ℝ) ≤ ((q * Pe e T : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (by positivity) (Pe_pos e T)
    nlinarith
  have hcardPow : ((I.powerset.erase ∅).card : ℝ) ≤ 2 ^ I.card := by
    rw [card_erase_of_mem (empty_mem_powerset I), card_powerset]
    have : 1 ≤ 2 ^ I.card := Nat.one_le_two_pow
    push_cast [Nat.cast_sub this]
    linarith
  have hsum2 : ∑ B ∈ I.powerset.erase ∅, |S B| ≤ 2 ^ I.card * G := by
    calc ∑ B ∈ I.powerset.erase ∅, |S B| ≤ ∑ B ∈ I.powerset.erase ∅, G := sum_le_sum hSB
      _ = ((I.powerset.erase ∅).card : ℝ) * G := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ I.card * G := by gcongr
  -- (4) `S ∅ = #C`, bounded by Brun–Titchmarsh
  have hS0 : S ∅ = C.card := by simp [hS]
  have hqN' : q < N := by
    have h1 : 2 ≤ q := Nat.le_self_pow (by omega) 2
    have h2 : q * 2 ≤ q ^ 4 := by
      calc q * 2 ≤ q * q := Nat.mul_le_mul_left q h1
        _ ≤ q * q * (q * q) := Nat.le_mul_of_pos_right _ (by positivity)
        _ = q ^ 4 := by ring
    omega
  have hBTC := hBT N q (1 + 2 ^ e) Nat.one_le_two_pow hqN'
    (by
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      have h5 : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
      omega)
  have hφq : (Nat.totient q : ℝ) = 2 ^ e := by
    rw [hq, Nat.totient_prime_pow Nat.prime_two (by omega)]
    push_cast
    ring
  rw [hφq] at hBTC
  have hlogq := log_three_quarter (k := e + 1) hqN
  have hCcard : (C.card : ℝ) * (2 ^ e * ((3 / 4) * Real.log N)) ≤ 2 * N := by
    have h1 : (C.card : ℝ) = primesInAP N q (1 + 2 ^ e) := rfl
    calc (C.card : ℝ) * (2 ^ e * ((3 / 4) * Real.log N))
        ≤ (C.card : ℝ) * (2 ^ e * Real.log ((N : ℝ) / (q : ℕ))) := by gcongr
      _ ≤ 2 * N := by rw [h1]; exact hBTC
  -- `(1/2)^(T-e) #C ≤ 8N / (3 · 2^T log N)`
  have hIcard : I.card = T - e := Nat.card_Ico e T
  have h2pow : (2 : ℝ) ^ T = 2 ^ (T - e) * 2 ^ e := by
    rw [← pow_add, Nat.sub_add_cancel heT.le]
  have hmain : (1 / 2 : ℝ) ^ I.card * C.card ≤ 8 * N / (3 * 2 ^ T * Real.log N) := by
    rw [hIcard, le_div_iff₀ (by positivity), h2pow]
    have h1 : (1 / 2 : ℝ) ^ (T - e) * 2 ^ (T - e) = 1 := by
      rw [← mul_pow]; norm_num
    calc (1 / 2 : ℝ) ^ (T - e) * C.card * (3 * (2 ^ (T - e) * 2 ^ e) * Real.log N)
        = 4 * ((1 / 2 : ℝ) ^ (T - e) * 2 ^ (T - e)) *
            ((C.card : ℝ) * (2 ^ e * ((3 / 4) * Real.log N))) := by ring
      _ ≤ 4 * 1 * (2 * N) := by rw [h1]; gcongr
      _ = 8 * N := by ring
  -- (5) `log (M_e N) ≤ 2^(T+1) + log N`
  have hlogM : Real.log (((q * Pe e T : ℕ) : ℝ) * N) ≤ 2 ^ (T + 1) + Real.log N := by
    have hMle : q * Pe e T ≤ 2 ^ T * 2 ^ (2 ^ T) :=
      Nat.mul_le_mul hqT (prod_F_Ico_lt e T).le
    have hMpos : (0 : ℝ) < ((q * Pe e T : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (by positivity) (Pe_pos e T)
    rw [Real.log_mul hMpos.ne' (by linarith)]
    have h1 : Real.log ((q * Pe e T : ℕ) : ℝ) ≤ Real.log ((2 : ℝ) ^ (T + 2 ^ T)) := by
      apply Real.log_le_log hMpos
      rw [pow_add]
      exact_mod_cast hMle
    rw [Real.log_pow, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] at h1
    have hT : (T : ℝ) + 2 ^ T ≤ 2 ^ (T + 1) := by
      have : (T : ℝ) ≤ 2 ^ T := by exact_mod_cast Nat.lt_two_pow_self.le
      rw [pow_succ]; linarith
    have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    have h3 : ((T : ℝ) + 2 ^ T) * Real.log 2 ≤ ((T : ℝ) + 2 ^ T) * 1 :=
      mul_le_mul_of_nonneg_left hl2.le (by positivity)
    linarith
  -- assembling
  calc (Se.card : ℝ) ≤ ∑ p ∈ C, w p := hcard
    _ = (1 / 2) ^ I.card * ∑ B ∈ I.powerset, (-1) ^ B.card * S B := hexp
    _ ≤ (1 / 2) ^ I.card * (S ∅ + 2 ^ I.card * G) := by
        gcongr
        exact hsplit.trans (_root_.add_le_add le_rfl hsum2)
    _ = (1 / 2) ^ I.card * C.card + G := by
        rw [hS0, mul_add, ← mul_assoc, ← mul_pow]
        norm_num
    _ ≤ 8 * N / (3 * 2 ^ T * Real.log N) + c₀ * Real.sqrt N * (2 ^ (T + 1) + Real.log N) :=
        _root_.add_le_add hmain (by rw [hGdef]; gcongr)

/-- The primes with `e_p ≥ T` in the proof of Theorem 1.2: at most `16N / (3 · 2^T log N)`. -/
theorem grh_big_block (hBT : BrunTitchmarsh) {N T : ℕ} (hT : 1 ≤ T) (hN : (2 ^ T) ^ 4 ≤ N) :
    (((eliteSet N).filter (fun p => T ≤ ev p)).card : ℝ) ≤ 16 * N / (3 * 2 ^ T * Real.log N) := by
  classical
  set Sb := (eliteSet N).filter (fun p => T ≤ ev p) with hSb
  have hsub : Sb.card ≤ primesInAP N (2 ^ T) 1 := by
    apply card_le_card
    intro p hp
    simp only [hSb, eliteSet, mem_filter, mem_range] at hp
    obtain ⟨⟨hpN, hpe⟩, hTe⟩ := hp
    simp only [mem_filter, mem_range]
    exact ⟨hpN, hpe.1, mod_pow_of_le_ev hpe.1 hTe⟩
  have h2T : 2 ≤ 2 ^ T := Nat.le_self_pow (by omega) 2
  have hqN : 2 ^ T < N := by
    have h2 : 2 ^ T * 2 ≤ (2 ^ T) ^ 4 := by
      calc 2 ^ T * 2 ≤ 2 ^ T * 2 ^ T := Nat.mul_le_mul_left _ h2T
        _ ≤ 2 ^ T * 2 ^ T * (2 ^ T * 2 ^ T) := Nat.le_mul_of_pos_right _ (by positivity)
        _ = (2 ^ T) ^ 4 := by ring
    omega
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hBT1 := hBT N (2 ^ T) 1 Nat.one_le_two_pow hqN (Nat.coprime_one_left _)
  have hφ : (Nat.totient (2 ^ T) : ℝ) = 2 ^ (T - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
    push_cast
    ring
  rw [hφ] at hBT1
  have hlog := log_three_quarter (k := T) hN
  have h2pow : (2 : ℝ) ^ T = 2 * 2 ^ (T - 1) := by
    have hT' : T = (T - 1) + 1 := by omega
    conv_lhs => rw [hT']
    rw [pow_succ]; ring
  have hcardR : (Sb.card : ℝ) ≤ primesInAP N (2 ^ T) 1 := by exact_mod_cast hsub
  rw [le_div_iff₀ (by positivity)]
  calc (Sb.card : ℝ) * (3 * 2 ^ T * Real.log N)
      = 8 * ((Sb.card : ℝ) * (2 ^ (T - 1) * ((3 / 4) * Real.log N))) := by rw [h2pow]; ring
    _ ≤ 8 * ((primesInAP N (2 ^ T) 1 : ℝ) *
          (2 ^ (T - 1) * Real.log ((N : ℝ) / ((2 ^ T : ℕ) : ℝ)))) := by gcongr
    _ ≤ 8 * (2 * N) := by gcongr
    _ = 16 * N := by ring

/-- Theorem 1.2, explicit form: under Brun–Titchmarsh and Lemma 4.1 (constant `c₀`), for
`T ≥ 1` and `(2^T)^4 ≤ N`,
`E(N) ≤ (T + 1) · 8N / (3 · 2^T log N) + T c₀ √N (2^(T+1) + log N)`. -/
theorem theoremB_explicit (hBT : BrunTitchmarsh) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hG : GRHCharSumWith c₀) {N T : ℕ} (hT : 1 ≤ T) (hN : (2 ^ T) ^ 4 ≤ N) :
    (E N : ℝ) ≤ (T + 1) * (8 * N / (3 * 2 ^ T * Real.log N)) +
      T * (c₀ * Real.sqrt N * (2 ^ (T + 1) + Real.log N)) := by
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
  set A : ℝ := 8 * N / (3 * 2 ^ T * Real.log N) with hA
  set G : ℝ := c₀ * Real.sqrt N * (2 ^ (T + 1) + Real.log N) with hGd
  have hN1 : 1 ≤ N := le_trans (Nat.one_le_pow _ _ (by positivity)) hN
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hG0 : 0 ≤ G := by positivity
  have hB : (16 * N / (3 * 2 ^ T * Real.log N) : ℝ) = 2 * A := by rw [hA]; ring
  calc (E N : ℝ)
      ≤ ∑ e ∈ Ico 1 T, (((eliteSet N).filter (fun p => ev p = e)).card : ℝ) +
          (((eliteSet N).filter (fun p => T ≤ ev p)).card : ℝ) := by exact_mod_cast hcardle
    _ ≤ ∑ e ∈ Ico 1 T, (A + G) + 16 * N / (3 * 2 ^ T * Real.log N) := by
        apply _root_.add_le_add
        · apply sum_le_sum
          intro e he
          rw [mem_Ico] at he
          exact grh_block_bound hBT hc₀ hG he.1 he.2 hN
        · exact grh_big_block hBT hT hN
    _ = ((T : ℝ) - 1) * (A + G) + 2 * A := by
        rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hT, hB]
        push_cast
        ring
    _ ≤ (T + 1) * A + T * G := by
        have h : ((T : ℝ) - 1) * (A + G) + 2 * A = (T + 1) * A + T * G - G := by ring
        linarith

/-- **Theorem 1.2.** Assuming Brun–Titchmarsh and Lemma 4.1 (a consequence of GRH),
`E(N) ≪ N^(3/4) (log N)^(1/2)`; explicitly `E(N) ≤ (16/3 + 3 c₀) N^(3/4) √(log N)` for
`N ≥ 2^72`. -/
theorem theoremB (hBT : BrunTitchmarsh) (hGRH : GRHCharSum) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (E N : ℝ) ≤ C * (N : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt (Real.log N) := by
  obtain ⟨c₀, hc₀, hG⟩ := hGRH
  refine ⟨16 / 3 + 3 * c₀, 2 ^ 72, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNbig : (512 : ℝ) ^ 8 ≤ N := by
    have : ((2 ^ 72 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    norm_num at this ⊢
    exact this
  -- `s = N^(1/8)`
  set s : ℝ := (N : ℝ) ^ ((1 : ℝ) / 8) with hsdef
  have hs0 : 0 ≤ s := Real.rpow_nonneg hN0 _
  have hs8 : s ^ 8 = N := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
  have hs6 : (N : ℝ) ^ ((3 : ℝ) / 4) = s ^ 6 := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
  have hs512 : 512 ≤ s := by
    by_contra h
    have h1 := pow_lt_pow_left₀ (lt_of_not_ge h) hs0 (by norm_num : (8 : ℕ) ≠ 0)
    rw [hs8] at h1
    linarith
  have hspos : 0 < s := by linarith
  have hsqrtN : Real.sqrt N = s ^ 4 := by
    rw [← hs8, show s ^ 8 = (s ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  -- `L = log N = 8 log s`, and `8 ≤ L ≤ 8 s`
  set L := Real.log N with hLdef
  have hL8 : L = 8 * Real.log s := by rw [hLdef, ← hs8, Real.log_pow]; norm_num
  have hlogs1 : 1 ≤ Real.log s := by
    rw [Real.le_log_iff_exp_le hspos]
    linarith [Real.exp_one_lt_d9]
  have hlogs : Real.log s ≤ s := le_trans (Real.log_le_sub_one_of_pos hspos) (by linarith)
  have hL1 : 8 ≤ L := by linarith
  have hLs : L ≤ 8 * s := by linarith
  -- `r = √L`, with `r^3 ≤ s^2`
  set r := Real.sqrt L with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hrr : r ^ 2 = L := Real.sq_sqrt (by linarith)
  have hr1 : 1 ≤ r := by nlinarith
  have hL3 : L ^ 3 ≤ s ^ 4 := by
    calc L ^ 3 ≤ (8 * s) ^ 3 := by gcongr
      _ = 512 * s ^ 3 := by ring
      _ ≤ s * s ^ 3 := by gcongr
      _ = s ^ 4 := by ring
  have hr3 : r ^ 3 ≤ s ^ 2 := by
    have h1 : (r ^ 3) ^ 2 ≤ (s ^ 2) ^ 2 := by
      calc (r ^ 3) ^ 2 = (r ^ 2) ^ 3 := by ring
        _ = L ^ 3 := by rw [hrr]
        _ ≤ s ^ 4 := hL3
        _ = (s ^ 2) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h1
  -- `Y = s^2 / r` and `T = ⌊log₂ Y⌋`
  set Y : ℝ := s ^ 2 / r with hYdef
  have hY2 : 2 ≤ Y := by
    rw [hYdef, le_div_iff₀ hr0]
    have hs3 : s ≤ s ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    have h1 : 4 * L ≤ s ^ 4 := by
      have : 32 * s ≤ s ^ 3 * s := by nlinarith
      calc 4 * L ≤ 32 * s := by linarith
        _ ≤ s ^ 3 * s := this
        _ = s ^ 4 := by ring
    have h2 : (2 * r) ^ 2 ≤ (s ^ 2) ^ 2 := by
      calc (2 * r) ^ 2 = 4 * r ^ 2 := by ring
        _ = 4 * L := by rw [hrr]
        _ ≤ s ^ 4 := h1
        _ = (s ^ 2) ^ 2 := by ring
    have h3 := (pow_le_pow_iff_left₀ (a := 2 * r) (b := s ^ 2) (n := 2) (by positivity)
      (by positivity) (by norm_num)).mp h2
    linarith
  have hYs : Y ≤ s ^ 2 := by rw [hYdef]; exact div_le_self (by positivity) hr1
  have hfl : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY2)
  set T := Nat.log 2 ⌊Y⌋₊ with hTdef
  have hT1 : 1 ≤ T := Nat.log_pos (by norm_num) hfl
  have h2TY : (2 : ℝ) ^ T ≤ Y := by
    have h1 : 2 ^ T ≤ ⌊Y⌋₊ := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2 ^ T : ℕ) : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact le_trans h2 (Nat.floor_le (by linarith))
  have hY2T : Y < 2 * 2 ^ T := by
    have h1 : ⌊Y⌋₊ < 2 ^ (T + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 : ⌊Y⌋₊ + 1 ≤ 2 * 2 ^ T := by rw [pow_succ] at h1; omega
    have h3 : (⌊Y⌋₊ : ℝ) + 1 ≤ 2 * 2 ^ T := by exact_mod_cast h2
    linarith [Nat.lt_floor_add_one Y]
  have hTN : (2 ^ T) ^ 4 ≤ N := by
    have h1 : ((2 : ℝ) ^ T) ^ 4 ≤ (s ^ 2) ^ 4 := by gcongr; linarith
    have h2 : (((2 ^ T) ^ 4 : ℕ) : ℝ) ≤ N := by
      push_cast
      calc ((2 : ℝ) ^ T) ^ 4 ≤ (s ^ 2) ^ 4 := h1
        _ = s ^ 8 := by ring
        _ = N := hs8
    exact_mod_cast h2
  -- `T + 1 ≤ L`
  have hTL : (T : ℝ) + 1 ≤ L := by
    have h1 : Real.log ((2 : ℝ) ^ T) ≤ Real.log (s ^ 2) :=
      Real.log_le_log (by positivity) (le_trans h2TY hYs)
    rw [Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h3 : (T : ℝ) * (1 / 2) ≤ T * Real.log 2 := mul_le_mul_of_nonneg_left hl2 (by positivity)
    linarith
  have hE := theoremB_explicit hBT (by linarith) hG hT1 hTN
  rw [← hLdef, hsqrtN, ← hs8] at hE
  rw [hs6]
  -- the main term
  have hmain : ((T : ℝ) + 1) * (8 * s ^ 8 / (3 * 2 ^ T * L)) ≤ (16 / 3) * s ^ 6 * r := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have h1 : s ^ 2 < 2 * 2 ^ T * r := by
      rw [hYdef, div_lt_iff₀ hr0] at hY2T; linarith
    calc ((T : ℝ) + 1) * (8 * s ^ 8) ≤ L * (8 * s ^ 8) := by gcongr
      _ = 8 * s ^ 6 * L * s ^ 2 := by ring
      _ ≤ 8 * s ^ 6 * L * (2 * 2 ^ T * r) := by gcongr
      _ = 16 / 3 * s ^ 6 * r * (3 * 2 ^ T * L) := by ring
  -- the error term
  have herr : (T : ℝ) * (c₀ * s ^ 4 * (2 ^ (T + 1) + L)) ≤ 3 * c₀ * s ^ 6 * r := by
    have h1 : (2 : ℝ) ^ (T + 1) ≤ 2 * Y := by rw [pow_succ]; linarith
    have hLY : L * Y = r * s ^ 2 := by
      rw [hYdef, ← hrr]; field_simp
    have h4 : s ^ 4 * r ^ 4 ≤ s ^ 6 * r := by
      have : s ^ 4 * r ^ 4 = (s ^ 4 * r) * r ^ 3 := by ring
      rw [this]
      calc (s ^ 4 * r) * r ^ 3 ≤ (s ^ 4 * r) * s ^ 2 := by gcongr
        _ = s ^ 6 * r := by ring
    calc (T : ℝ) * (c₀ * s ^ 4 * (2 ^ (T + 1) + L))
        ≤ L * (c₀ * s ^ 4 * (2 * Y + L)) := by
          gcongr
          linarith
      _ = c₀ * (2 * s ^ 4 * (L * Y) + s ^ 4 * L ^ 2) := by ring
      _ = c₀ * (2 * s ^ 6 * r + s ^ 4 * r ^ 4) := by rw [hLY, ← hrr]; ring
      _ ≤ c₀ * (2 * s ^ 6 * r + s ^ 6 * r) := by gcongr
      _ = 3 * c₀ * s ^ 6 * r := by ring
  calc (E N : ℝ) ≤ ((T : ℝ) + 1) * (8 * s ^ 8 / (3 * 2 ^ T * L)) +
        T * (c₀ * s ^ 4 * (2 ^ (T + 1) + L)) := hE
    _ ≤ (16 / 3) * s ^ 6 * r + 3 * c₀ * s ^ 6 * r := _root_.add_le_add hmain herr
    _ = (16 / 3 + 3 * c₀) * s ^ 6 * r := by ring

end ElitePrimes
