import Mathlib

/-!
# Elite primes: definitions and facts about Fermat numbers

See `README.md` for the correspondence with the paper.
-/

namespace ElitePrimes

open Nat Finset

/-- The `n`-th Fermat number; definitionally `2 ^ (2 ^ n) + 1`. -/
abbrev F (n : ℕ) : ℕ := Nat.fermatNumber n

theorem F_def (n : ℕ) : F n = 2 ^ (2 ^ n) + 1 := rfl

/-- An odd prime `p` is elite if `J(F n | p) = -1` for all large `n`.
For prime `p` the Jacobi symbol is the Legendre symbol. -/
def IsElite (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, jacobiSym (F n) p = -1

/-- `ev p = e_p = v₂(p - 1)`. -/
noncomputable def ev (p : ℕ) : ℕ := padicValNat 2 (p - 1)

theorem F_pos (n : ℕ) : 0 < F n := by
  rw [F_def]; positivity

theorem F_odd (n : ℕ) : F n % 2 = 1 := by
  have h2 : 2 ∣ 2 ^ (2 ^ n) := dvd_pow_self 2 (pow_ne_zero n (by norm_num))
  have h := Nat.mod_eq_zero_of_dvd h2
  rw [F_def]; omega

theorem four_dvd_two_pow_two_pow {n : ℕ} (hn : 1 ≤ n) : 4 ∣ 2 ^ (2 ^ n) := by
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h : 2 ^ 2 ∣ 2 ^ (2 ^ n) := Nat.pow_dvd_pow 2 h2
  simpa using h

theorem F_mod_four {n : ℕ} (hn : 1 ≤ n) : F n % 4 = 1 := by
  have h := Nat.mod_eq_zero_of_dvd (four_dvd_two_pow_two_pow hn)
  rw [F_def]; omega

theorem F_mod_three {n : ℕ} (hn : 1 ≤ n) : F n % 3 = 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h : 2 ^ (2 ^ (m + 1)) % 3 = 1 := by
    -- 2^(2^(m+1)) = (2^2)^(2^m) = 4^(2^m) ≡ 1 (mod 3)
    rw [pow_succ, pow_mul', Nat.pow_mod]
    norm_num
  rw [F_def]; omega

theorem coprime_two_F (n : ℕ) : Nat.Coprime 2 (F n) := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro h
  have h1 := Nat.mod_eq_zero_of_dvd h
  have h2 := F_odd n
  omega

theorem coprime_three_F {n : ℕ} (hn : 1 ≤ n) : Nat.Coprime 3 (F n) := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h
  have h1 := Nat.mod_eq_zero_of_dvd h
  have h2 := F_mod_three hn
  omega

/-- `J(3 | F n) = -1` for `n ≥ 1`: reciprocity (`F n ≡ 1 mod 4`) and `F n ≡ 2 mod 3`. -/
theorem jacobi_three_F {n : ℕ} (hn : 1 ≤ n) : jacobiSym 3 (F n) = -1 := by
  have hrec := jacobiSym.quadratic_reciprocity_one_mod_four (a := F n) (b := 3)
    (F_mod_four hn) ⟨1, by norm_num⟩
  -- hrec : J(F n | 3) = J(↑3 | F n)
  simp only [Nat.cast_ofNat] at hrec
  rw [← hrec]
  have hmod : ((F n : ℕ) : ℤ) % ((3 : ℕ) : ℤ) = (2 : ℤ) % ((3 : ℕ) : ℤ) := by
    have h3 := F_mod_three hn
    push_cast
    omega
  rw [jacobiSym.mod_left' hmod]
  -- J(2 | 3) = -1; evaluated by the `norm_num` extension for Jacobi symbols
  norm_num

/-- Lemma 2.1 (F1): distinct Fermat numbers are coprime
(mathlib: `Nat.coprime_fermatNumber_fermatNumber`). -/
theorem F_coprime {m n : ℕ} (h : m ≠ n) : Nat.Coprime (F m) (F n) :=
  Nat.coprime_fermatNumber_fermatNumber h

/-- Lemma 2.1 (F1): `∏_{k < n} F k = 2^(2^n) - 1` (mathlib: `Nat.prod_fermatNumber`). -/
theorem prod_F_range (n : ℕ) : ∏ k ∈ range n, F k = 2 ^ (2 ^ n) - 1 := by
  show ∏ k ∈ range n, Nat.fermatNumber k = 2 ^ (2 ^ n) - 1
  rw [Nat.prod_fermatNumber]
  show (2 ^ (2 ^ n) + 1) - 2 = 2 ^ (2 ^ n) - 1
  omega

/-- A product of consecutive Fermat numbers below index `T` is `< 2^(2^T)`. -/
theorem prod_F_Ico_lt (e T : ℕ) : ∏ k ∈ Ico e T, F k < 2 ^ (2 ^ T) := by
  have hsub : Ico e T ⊆ range T := by
    intro k hk
    simp only [mem_Ico, mem_range] at hk ⊢
    omega
  have hdvd := Finset.prod_dvd_prod_of_subset _ _ F hsub
  have hpos : 0 < ∏ k ∈ range T, F k := Finset.prod_pos (fun k _ => F_pos k)
  have hle := Nat.le_of_dvd hpos hdvd
  rw [prod_F_range] at hle
  have h2 : 0 < 2 ^ (2 ^ T) := by positivity
  omega

/-- Congruent numerators give equal Jacobi symbols (natural-number version). -/
theorem jacobi_congr {a b D : ℕ} (h : a ≡ b [MOD D]) :
    jacobiSym a D = jacobiSym b D := by
  apply jacobiSym.mod_left'
  have h' : a % D = b % D := h
  exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) h'

end ElitePrimes
