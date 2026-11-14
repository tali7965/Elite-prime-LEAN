import ElitePrimes.Basic

/-!
# Lemma 2.3: counting residue classes (by the route of Remark 2.4)

For `1 ≤ e ≤ T`, with `Pe e T = ∏_{e ≤ n < T} F n` and `Me e T = 2^(e+1) * Pe e T`, the units
`u mod Me e T` with `u ≡ 1 + 2^e (mod 2^(e+1))` and `J(u | F n) = -1` for all `e ≤ n < T`
number exactly `φ(Me e T) / 2^T` (`card_R_mul`).

Proof: the "signature" of a unit (residue mod `2^(e+1)`, set of `n` with `J = -1`) takes each of
the `2^T` possible values equally often, because multiplying by a suitable unit `c`
(built by the Chinese remainder theorem, using `J(3 | F n) = -1`) moves one fibre onto another.
-/

namespace ElitePrimes

open Nat Finset

/-- Abstract equal-fibres lemma. -/
theorem card_fiber_mul_card {G Y : Type*} [Group G] [Fintype G] [DecidableEq Y]
    (σ : G → Y) (S : Finset Y) (hS : ∀ g, σ g ∈ S) (y₀ : Y)
    (hmove : ∀ y ∈ S, ∃ c : G, ∀ g, σ (c * g) = y ↔ σ g = y₀) :
    (univ.filter (fun g => σ g = y₀)).card * S.card = Fintype.card G := by
  have hsum : Fintype.card G = ∑ y ∈ S, (univ.filter (fun g => σ g = y)).card :=
    card_eq_sum_card_fiberwise (fun g _ => hS g)
  have hconst : ∀ y ∈ S, (univ.filter (fun g => σ g = y)).card =
      (univ.filter (fun g => σ g = y₀)).card := by
    intro y hy
    obtain ⟨c, hc⟩ := hmove y hy
    symm
    apply Finset.card_nbij' (fun g => c * g) (fun g => c⁻¹ * g)
    · intro g hg
      simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hg ⊢
      exact (hc g).mpr hg
    · intro g hg
      simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hg ⊢
      have h := (hc (c⁻¹ * g)).mp
      rw [mul_inv_cancel_left] at h
      exact h hg
    · intro g _; simp
    · intro g _; simp
  rw [hsum, sum_congr rfl hconst, sum_const, smul_eq_mul, mul_comm]

/-- `Pe e T = ∏_{e ≤ n < T} F n`. -/
def Pe (e T : ℕ) : ℕ := ∏ n ∈ Ico e T, F n

/-- `Me e T = 2^(e+1) * Pe e T`. -/
def Me (e T : ℕ) : ℕ := 2 ^ (e + 1) * Pe e T

theorem Pe_pos (e T : ℕ) : 0 < Pe e T := prod_pos (fun n _ => F_pos n)

theorem Me_pos (e T : ℕ) : 0 < Me e T := Nat.mul_pos (by positivity) (Pe_pos e T)

instance (e T : ℕ) : NeZero (Me e T) := ⟨(Me_pos e T).ne'⟩

theorem F_dvd_Me {e T n : ℕ} (hn : n ∈ Ico e T) : F n ∣ Me e T :=
  dvd_mul_of_dvd_right (dvd_prod_of_mem F hn) _

theorem two_pow_dvd_Me (e T : ℕ) : 2 ^ (e + 1) ∣ Me e T := dvd_mul_right _ _

/-- The signature of a unit modulo `Me e T`. -/
noncomputable def sig (e T : ℕ) (u : (ZMod (Me e T))ˣ) : ℕ × Finset ℕ :=
  ((u : ZMod (Me e T)).val % 2 ^ (e + 1),
   (Ico e T).filter (fun n => jacobiSym ((u : ZMod (Me e T)).val : ℤ) (F n) = -1))

/-- The admissible classes `R_e` of Lemma 2.3. -/
noncomputable def Rset (e T : ℕ) : Finset (ZMod (Me e T))ˣ :=
  univ.filter (fun u => sig e T u = (1 + 2 ^ e, Ico e T))

/-- All possible signatures: an odd residue below `2^(e+1)` and a subset of `[e, T)`. -/
def targets (e T : ℕ) : Finset (ℕ × Finset ℕ) :=
  ((range (2 ^ e)).image (fun k => 2 * k + 1)) ×ˢ (Ico e T).powerset

theorem card_targets {e T : ℕ} (heT : e ≤ T) : (targets e T).card = 2 ^ T := by
  rw [targets, card_product, Finset.card_image_of_injective _ (fun a b h => by omega),
    card_range, card_powerset, Nat.card_Ico, ← pow_add, Nat.add_sub_cancel' heT]

theorem sig_mem {e T : ℕ} (u : (ZMod (Me e T))ˣ) : sig e T u ∈ targets e T := by
  have hcop : Nat.Coprime (u : ZMod (Me e T)).val (Me e T) := ZMod.val_coe_unit_coprime u
  have h2 : 2 ∣ Me e T := dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero e)) (two_pow_dvd_Me e T)
  have hc2 : Nat.Coprime 2 (u : ZMod (Me e T)).val :=
    Nat.coprime_comm.mp (Nat.Coprime.coprime_dvd_right h2 hcop)
  have hodd : (u : ZMod (Me e T)).val % 2 = 1 := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at hc2
    omega
  have hr2 : (u : ZMod (Me e T)).val % 2 ^ (e + 1) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (Nat.succ_ne_zero e))]; exact hodd
  have hrlt : (u : ZMod (Me e T)).val % 2 ^ (e + 1) < 2 ^ (e + 1) := Nat.mod_lt _ (by positivity)
  have hpow : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
  simp only [sig, targets, mem_product, mem_image, mem_range, mem_powerset]
  -- name the residue so that `omega` treats it as an atom
  generalize hr : (u : ZMod (Me e T)).val % 2 ^ (e + 1) = r at hr2 hrlt ⊢
  generalize hq : 2 ^ e = q at hpow ⊢
  refine ⟨⟨r / 2, ?_, ?_⟩, filter_subset _ _⟩
  · omega
  · omega

/-- `(1 + 2^e)^2 ≡ 1 (mod 2^(e+1))` for `e ≥ 1`. -/
theorem one_add_two_pow_sq {e : ℕ} (he : 1 ≤ e) :
    (1 + 2 ^ e) * (1 + 2 ^ e) ≡ 1 [MOD 2 ^ (e + 1)] := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
  have h : (1 + 2 ^ (f + 1)) * (1 + 2 ^ (f + 1)) = 1 + 2 ^ (f + 1 + 1) * (1 + 2 ^ f) := by ring
  rw [h]
  show (1 + 2 ^ (f + 1 + 1) * (1 + 2 ^ f)) % 2 ^ (f + 1 + 1) = 1 % 2 ^ (f + 1 + 1)
  rw [Nat.add_mul_mod_self_left]

/-- Moving the fibre of `(1 + 2^e, [e,T))` onto the fibre of any other signature. -/
theorem exists_move {e T : ℕ} (he : 1 ≤ e) (k : ℕ) (hk : k < 2 ^ e) (B : Finset ℕ)
    (hB : B ⊆ Ico e T) :
    ∃ c : (ZMod (Me e T))ˣ, ∀ u,
      sig e T (c * u) = (2 * k + 1, B) ↔ sig e T u = (1 + 2 ^ e, Ico e T) := by
  classical
  let a : ℕ → ℕ := fun n => if n ∈ B then 1 else 3
  have ha : ∀ n, a n = if n ∈ B then 1 else 3 := fun n => rfl
  have hpair : Set.Pairwise (↑(Ico e T) : Set ℕ) (Function.onFun Nat.Coprime F) := by
    intro i _ j _ hij
    exact F_coprime hij
  obtain ⟨c₁, hc₁⟩ :=
    Nat.chineseRemainderOfFinset a F (Ico e T) (fun n _ => (F_pos n).ne') hpair
  have hcopP : Nat.Coprime (2 ^ (e + 1)) (Pe e T) :=
    Nat.Coprime.prod_right (fun n _ => Nat.Coprime.pow_left _ (coprime_two_F n))
  obtain ⟨c, hc2, hcP⟩ := Nat.chineseRemainder hcopP ((2 * k + 1) * (1 + 2 ^ e)) c₁
  have hcF : ∀ n ∈ Ico e T, c ≡ a n [MOD F n] := fun n hn =>
    (hcP.of_dvd (dvd_prod_of_mem F hn)).trans (hc₁ n hn)
  -- c is odd and coprime to every F n, hence a unit mod Me e T
  have hc₂odd : Odd ((2 * k + 1) * (1 + 2 ^ e)) := by
    refine Nat.odd_mul.mpr ⟨⟨k, rfl⟩, ?_⟩
    obtain ⟨f, hf⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
    exact ⟨2 ^ f, by rw [hf, pow_succ]; ring⟩
  have hc_odd : c % 2 = 1 := by
    have h1 : c ≡ (2 * k + 1) * (1 + 2 ^ e) [MOD 2] :=
      hc2.of_dvd (dvd_pow_self 2 (Nat.succ_ne_zero e))
    have h2 := Nat.odd_iff.mp hc₂odd
    have h3 : c % 2 = ((2 * k + 1) * (1 + 2 ^ e)) % 2 := h1
    omega
  have hcM : Nat.Coprime c (Me e T) := by
    show Nat.Coprime c (2 ^ (e + 1) * Pe e T)
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      omega
    · apply Nat.Coprime.prod_right
      intro n hn
      have hn1 : 1 ≤ n := le_trans he (mem_Ico.mp hn).1
      have hg : Nat.gcd c (F n) = Nat.gcd (a n) (F n) := (hcF n hn).gcd_eq
      show Nat.gcd c (F n) = 1
      rw [hg, ha]
      by_cases hnB : n ∈ B
      · simp [hnB]
      · simp only [hnB, if_false]; exact coprime_three_F hn1
  set cu : (ZMod (Me e T))ˣ := ZMod.unitOfCoprime c hcM with hcu
  -- value of c * u
  have hvaleq : ∀ u : (ZMod (Me e T))ˣ,
      ((cu * u : (ZMod (Me e T))ˣ) : ZMod (Me e T)).val
        = (c * (u : ZMod (Me e T)).val) % Me e T := by
    intro u
    rw [Units.val_mul, hcu, ZMod.coe_unitOfCoprime, ← ZMod.val_natCast]
    congr 1
    push_cast
    rw [ZMod.natCast_zmod_val]
  -- first component
  have hε := one_add_two_pow_sq he
  have hfirst : ∀ x : ℕ, (c * x) % 2 ^ (e + 1) = 2 * k + 1 ↔ x % 2 ^ (e + 1) = 1 + 2 ^ e := by
    intro x
    have hr'lt : 2 * k + 1 < 2 ^ (e + 1) := by rw [pow_succ]; omega
    have hεlt : 1 + 2 ^ e < 2 ^ (e + 1) := by
      have : 1 < 2 ^ e := Nat.one_lt_two_pow (by omega)
      rw [pow_succ]; omega
    have hcop' : Nat.Coprime (2 ^ (e + 1)) (2 * k + 1) := by
      apply Nat.Coprime.pow_left
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
    constructor
    · intro hx
      have h1 : c * x ≡ 2 * k + 1 [MOD 2 ^ (e + 1)] := by
        show (c * x) % _ = (2 * k + 1) % _
        rw [hx, Nat.mod_eq_of_lt hr'lt]
      have h2 : (2 * k + 1) * (1 + 2 ^ e) * x ≡ 2 * k + 1 [MOD 2 ^ (e + 1)] :=
        (hc2.mul_right x).symm.trans h1
      have h3 : (2 * k + 1) * x ≡ (2 * k + 1) * (1 + 2 ^ e) [MOD 2 ^ (e + 1)] := by
        have h4 := h2.mul_right (1 + 2 ^ e)
        have h5 : (2 * k + 1) * (1 + 2 ^ e) * x * (1 + 2 ^ e) =
            (2 * k + 1) * x * ((1 + 2 ^ e) * (1 + 2 ^ e)) := by ring
        rw [h5] at h4
        have h6 : (2 * k + 1) * x * ((1 + 2 ^ e) * (1 + 2 ^ e)) ≡ (2 * k + 1) * x * 1
            [MOD 2 ^ (e + 1)] := hε.mul_left _
        rw [mul_one] at h6
        exact h6.symm.trans h4
      have h7 : x ≡ 1 + 2 ^ e [MOD 2 ^ (e + 1)] := Nat.ModEq.cancel_left_of_coprime hcop' h3
      have h8 : x % 2 ^ (e + 1) = (1 + 2 ^ e) % 2 ^ (e + 1) := h7
      rw [h8, Nat.mod_eq_of_lt hεlt]
    · intro hx
      have hxm : x ≡ 1 + 2 ^ e [MOD 2 ^ (e + 1)] := by
        show x % _ = (1 + 2 ^ e) % _
        rw [hx, Nat.mod_eq_of_lt hεlt]
      have h1 : c * x ≡ (2 * k + 1) * (1 + 2 ^ e) * (1 + 2 ^ e) [MOD 2 ^ (e + 1)] :=
        hc2.mul hxm
      have h2 : (2 * k + 1) * (1 + 2 ^ e) * (1 + 2 ^ e) ≡ (2 * k + 1) * 1 [MOD 2 ^ (e + 1)] := by
        rw [mul_assoc]; exact hε.mul_left _
      have h3 : (c * x) % 2 ^ (e + 1) = ((2 * k + 1) * 1) % 2 ^ (e + 1) := h1.trans h2
      rw [h3, mul_one, Nat.mod_eq_of_lt hr'lt]
  -- second component
  have hJc : ∀ n ∈ Ico e T, jacobiSym (c : ℤ) (F n) = if n ∈ B then 1 else -1 := by
    intro n hn
    have hn1 : 1 ≤ n := le_trans he (mem_Ico.mp hn).1
    rw [jacobi_congr (hcF n hn), ha]
    by_cases hnB : n ∈ B
    · simp only [hnB, if_true, Nat.cast_one]; exact jacobiSym.one_left (F n)
    · simp only [hnB, if_false, Nat.cast_ofNat]; exact jacobi_three_F hn1
  have hux : ∀ u : (ZMod (Me e T))ˣ, ∀ n ∈ Ico e T, Nat.Coprime (u : ZMod (Me e T)).val (F n) :=
    fun u n hn => Nat.Coprime.coprime_dvd_right (F_dvd_Me hn) (ZMod.val_coe_unit_coprime u)
  have hsecond : ∀ u : (ZMod (Me e T))ˣ,
      (Ico e T).filter (fun n => jacobiSym
          (((c * (u : ZMod (Me e T)).val) % Me e T : ℕ) : ℤ) (F n) = -1) = B ↔
      (Ico e T).filter (fun n => jacobiSym ((u : ZMod (Me e T)).val : ℤ) (F n) = -1)
          = Ico e T := by
    intro u
    have hprod : ∀ n ∈ Ico e T,
        jacobiSym (((c * (u : ZMod (Me e T)).val) % Me e T : ℕ) : ℤ) (F n) =
        (if n ∈ B then 1 else -1) * jacobiSym ((u : ZMod (Me e T)).val : ℤ) (F n) := by
      intro n hn
      rw [jacobi_congr ((Nat.mod_modEq _ _).of_dvd (F_dvd_Me hn)), Nat.cast_mul,
        jacobiSym.mul_left, hJc n hn]
    have hpm : ∀ n ∈ Ico e T, jacobiSym ((u : ZMod (Me e T)).val : ℤ) (F n) = 1 ∨
        jacobiSym ((u : ZMod (Me e T)).val : ℤ) (F n) = -1 := by
      intro n hn
      apply jacobiSym.eq_one_or_neg_one
      rw [Int.gcd_natCast_natCast]
      exact hux u n hn
    constructor
    · intro hB'
      apply Finset.filter_true_of_mem
      intro n hn
      have hmem : n ∈ B ↔ jacobiSym (((c * (u : ZMod (Me e T)).val) % Me e T : ℕ) : ℤ) (F n)
          = -1 := by
        rw [← hB', Finset.mem_filter]; simp [hn]
      rw [hprod n hn] at hmem
      by_cases hnB : n ∈ B
      · have h := hmem.mp hnB
        simpa [hnB] using h
      · rcases hpm n hn with h1 | h1
        · exfalso; apply hnB; apply hmem.mpr; rw [if_neg hnB, h1]; norm_num
        · exact h1
    · intro hall
      have hxm : ∀ n ∈ Ico e T, jacobiSym ((u : ZMod (Me e T)).val : ℤ) (F n) = -1 := by
        intro n hn
        have h : n ∈ (Ico e T).filter
            (fun n => jacobiSym ((u : ZMod (Me e T)).val : ℤ) (F n) = -1) := by
          rw [hall]; exact hn
        exact (Finset.mem_filter.mp h).2
      ext n
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hn, hJ⟩
        rw [hprod n hn, hxm n hn] at hJ
        by_contra hnB
        simp [hnB] at hJ
      · intro hnB
        have hn : n ∈ Ico e T := hB hnB
        refine ⟨hn, ?_⟩
        rw [hprod n hn, hxm n hn]
        simp [hnB]
  refine ⟨cu, fun u => ?_⟩
  simp only [sig, Prod.mk.injEq]
  rw [hvaleq u, Nat.mod_mod_of_dvd _ (two_pow_dvd_Me e T)]
  exact and_congr (hfirst _) (hsecond u)

/-- **Lemma 2.3.** `|R_e| * 2^T = φ(M_e)`. -/
theorem card_R_mul {e T : ℕ} (he : 1 ≤ e) (heT : e ≤ T) :
    (Rset e T).card * 2 ^ T = Nat.totient (Me e T) := by
  classical
  have hmove : ∀ y ∈ targets e T, ∃ c : (ZMod (Me e T))ˣ, ∀ g,
      sig e T (c * g) = y ↔ sig e T g = (1 + 2 ^ e, Ico e T) := by
    rintro ⟨y1, y2⟩ hy
    simp only [targets, mem_product, mem_image, mem_range, mem_powerset] at hy
    obtain ⟨⟨k, hk, rfl⟩, hB⟩ := hy
    exact exists_move he k hk y2 hB
  have h := card_fiber_mul_card (sig e T) (targets e T) sig_mem (1 + 2 ^ e, Ico e T) hmove
  rw [card_targets heT, ZMod.card_units_eq_totient] at h
  exact h

end ElitePrimes
