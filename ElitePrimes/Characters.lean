import ElitePrimes.Count

/-!
# Jacobi symbols as Dirichlet characters; Lemma 2.1 (F3)

* `jacChar B m` : `χ_B = ∏_{n ∈ B} (· / F n)` as a Dirichlet character modulo a multiple `m`
  of every `F n`, `n ∈ B` (it is `0` on non-units).
* `F3`          : **Lemma 2.1 (F3)**.
* `sum_filter_eq_char_sum` : orthogonality, used to pick out a residue class.
-/

namespace ElitePrimes

open Nat Finset

theorem jacobi_val_mul {m n : ℕ} (h : F n ∣ m) (a b : ZMod m) :
    jacobiSym ((a * b).val : ℤ) (F n) =
      jacobiSym (a.val : ℤ) (F n) * jacobiSym (b.val : ℤ) (F n) := by
  rw [ZMod.val_mul, jacobi_congr ((Nat.mod_modEq _ _).of_dvd h), Nat.cast_mul, jacobiSym.mul_left]

theorem jacobi_val_natCast {m n : ℕ} (h : F n ∣ m) (k : ℕ) :
    jacobiSym (((k : ZMod m)).val : ℤ) (F n) = jacobiSym (k : ℤ) (F n) := by
  rw [ZMod.val_natCast, jacobi_congr ((Nat.mod_modEq _ _).of_dvd h)]

open Classical in
/-- `χ_B` as a Dirichlet character modulo `m`, where `F n ∣ m` for every `n ∈ B`. -/
noncomputable def jacChar (B : Finset ℕ) (m : ℕ) (hB : ∀ n ∈ B, F n ∣ m) :
    DirichletCharacter ℂ m where
  toFun a := if IsUnit a then ∏ n ∈ B, ((jacobiSym (a.val : ℤ) (F n) : ℤ) : ℂ) else 0
  map_one' := by
    rw [ite_eq_left isUnit_one]
    apply Finset.prod_eq_one
    intro n hn
    rw [show (1 : ZMod m) = ((1 : ℕ) : ZMod m) by simp, jacobi_val_natCast (hB n hn)]
    simp [jacobiSym.one_left]
  map_mul' a b := by
    by_cases ha : IsUnit a
    · by_cases hb : IsUnit b
      · simp only [ite_eq_left (ha.mul hb), ite_eq_left ha, ite_eq_left hb]
        rw [← prod_mul_distrib]
        apply prod_congr rfl
        intro n hn
        rw [jacobi_val_mul (hB n hn)]
        push_cast
        ring
      · have : ¬ IsUnit (a * b) := fun h => hb (isUnit_of_mul_isUnit_right h)
        simp only [ite_eq_right this, ite_eq_right hb, mul_zero]
    · have : ¬ IsUnit (a * b) := fun h => ha (isUnit_of_mul_isUnit_left h)
      simp only [ite_eq_right this, ite_eq_right ha, zero_mul]
  map_nonunit' a ha := ite_eq_right ha

open Classical in
theorem jacChar_apply {B : Finset ℕ} {m : ℕ} (hB : ∀ n ∈ B, F n ∣ m) (a : ZMod m) :
    jacChar B m hB a =
      if IsUnit a then ∏ n ∈ B, ((jacobiSym (a.val : ℤ) (F n) : ℤ) : ℂ) else 0 := rfl

theorem jacChar_natCast {B : Finset ℕ} {m : ℕ} (hB : ∀ n ∈ B, F n ∣ m) {k : ℕ}
    (hk : Nat.Coprime k m) :
    jacChar B m hB (k : ZMod m) = ∏ n ∈ B, ((jacobiSym (k : ℤ) (F n) : ℤ) : ℂ) := by
  have hu : IsUnit (k : ZMod m) := (ZMod.isUnit_iff_coprime k m).mpr hk
  rw [jacChar_apply, ite_eq_left hu]
  apply prod_congr rfl
  intro n hn
  rw [jacobi_val_natCast (hB n hn)]

theorem jacChar_natCast_of_not {B : Finset ℕ} {m : ℕ} (hB : ∀ n ∈ B, F n ∣ m) {k : ℕ}
    (hk : ¬ Nat.Coprime k m) : jacChar B m hB (k : ZMod m) = 0 :=
  MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])

theorem changeLevel_natCast {Q m : ℕ} (h : Q ∣ m) (ψ : DirichletCharacter ℂ Q) {k : ℕ}
    (hk : Nat.Coprime k m) : ψ.changeLevel h (k : ZMod m) = ψ (k : ZMod Q) := by
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ h (ZMod.unitOfCoprime k hk)
  rw [ZMod.coe_unitOfCoprime] at this
  rw [this, ZMod.cast_natCast h]

/-- At natural numbers, `(ψ χ_B)(k) = ψ(k) χ_B(k)` with `ψ` evaluated modulo `Q`. -/
theorem mul_jacChar_natCast {Q m : ℕ} (h : Q ∣ m) (ψ : DirichletCharacter ℂ Q)
    {B : Finset ℕ} (hB : ∀ n ∈ B, F n ∣ m) (k : ℕ) :
    (ψ.changeLevel h * jacChar B m hB) (k : ZMod m) =
      ψ (k : ZMod Q) * jacChar B m hB (k : ZMod m) := by
  rw [MulChar.coeToFun_mul, Pi.mul_apply]
  by_cases hk : Nat.Coprime k m
  · rw [changeLevel_natCast h ψ hk]
  · rw [jacChar_natCast_of_not hB hk, mul_zero, mul_zero]

/-- A product of Fermat numbers divides every common multiple of them. -/
theorem prod_F_dvd {B : Finset ℕ} {M : ℕ} (h : ∀ n ∈ B, F n ∣ M) : ∏ n ∈ B, F n ∣ M := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert n B hn ih =>
    rw [prod_insert hn]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · exact Nat.Coprime.prod_right (fun k hk => F_coprime (fun hnk => hn (hnk ▸ hk)))
    · exact h n (mem_insert_self _ _)
    · exact ih (fun k hk => h k (mem_insert_of_mem hk))

/-- `J(2 | F 0) = J(2 | 3) = -1`. -/
theorem jacobi_two_F_zero : jacobiSym 2 (F 0) = -1 := by
  rw [show F 0 = 3 from rfl]
  norm_num

/-- **Lemma 2.1 (F3).** Let `B ≠ ∅`, let `M` be a multiple of `D_B = ∏_{n ∈ B} F n`, and let
`ψ` be a Dirichlet character modulo `Q` with `gcd(Q, M) = 1`. Then `ψ χ_B` is a non-principal
character modulo `QM`. -/
theorem F3 {B : Finset ℕ} (hBne : B.Nonempty) {Q M : ℕ} [NeZero Q] [NeZero M]
    (hBM : ∀ n ∈ B, F n ∣ M) (hQM : Nat.Coprime Q M) (ψ : DirichletCharacter ℂ Q) :
    ψ.changeLevel (dvd_mul_right Q M) *
      jacChar B (Q * M) (fun n hn => dvd_mul_of_dvd_right (hBM n hn) Q) ≠ 1 := by
  classical
  obtain ⟨n₀, hn₀⟩ := hBne
  -- target residues: `J(t n | F n) = -1` at `n₀`, `= 1` elsewhere
  let t : ℕ → ℕ := fun n => if n = n₀ then (if n₀ = 0 then 2 else 3) else 1
  have ht : ∀ n ∈ B, jacobiSym (t n : ℤ) (F n) = if n = n₀ then -1 else 1 := by
    intro n _
    by_cases h : n = n₀
    · subst h
      by_cases h0 : n = 0
      · subst h0; simpa [t] using jacobi_two_F_zero
      · simpa [t, h0] using jacobi_three_F (by omega)
    · simp [t, h, jacobiSym.one_left]
  have htcop : ∀ n ∈ B, Nat.Coprime (t n) (F n) := by
    intro n hn
    haveI : NeZero (F n) := ⟨(F_pos n).ne'⟩
    have h1 : jacobiSym (t n : ℤ) (F n) ≠ 0 := by
      rw [ht n hn]; split_ifs <;> norm_num
    have h2 : Int.gcd (t n : ℤ) (F n : ℤ) = 1 := by
      by_contra hc
      exact h1 ((jacobiSym.eq_zero_iff_not_coprime).mpr hc)
    rwa [Int.gcd_natCast_natCast] at h2
  -- Chinese remainder theorem: `c ≡ 1 (mod Q)` and `c ≡ t n (mod F n)`
  set D := ∏ n ∈ B, F n with hD
  have hpair : Set.Pairwise (B : Set ℕ) (Function.onFun Nat.Coprime F) :=
    fun i _ j _ hij => F_coprime hij
  obtain ⟨c₁, hc₁⟩ := Nat.chineseRemainderOfFinset t F B (fun n _ => (F_pos n).ne') hpair
  have hDM : D ∣ M := prod_F_dvd hBM
  have hQD : Nat.Coprime Q D :=
    Nat.Coprime.prod_right (fun n hn => Nat.Coprime.coprime_dvd_right (hBM n hn) hQM)
  obtain ⟨c, hcQ, hcD⟩ := Nat.chineseRemainder hQD 1 c₁
  have hcF : ∀ n ∈ B, c ≡ t n [MOD F n] := fun n hn =>
    (hcD.of_dvd (dvd_prod_of_mem F hn)).trans (hc₁ n hn)
  have hcop : Nat.Coprime c (Q * D) := by
    apply Nat.Coprime.mul_right
    · rw [Nat.Coprime, hcQ.gcd_eq]; simp
    · apply Nat.Coprime.prod_right
      intro n hn
      rw [Nat.Coprime, (hcF n hn).gcd_eq]
      exact htcop n hn
  -- lift the unit `c mod QD` to a unit `a mod QM`
  haveI : NeZero D := ⟨(prod_pos (fun n _ => F_pos n)).ne'⟩
  have hdiv : Q * D ∣ Q * M := mul_dvd_mul_left Q hDM
  obtain ⟨a, ha⟩ := ZMod.unitsMap_surjective hdiv (ZMod.unitOfCoprime c hcop)
  set v := (a : ZMod (Q * M)).val with hv
  have hva : ((v : ℕ) : ZMod (Q * M)) = a := ZMod.natCast_zmod_val _
  have hvc : v ≡ c [MOD Q * D] := by
    have h1 := congrArg Units.val ha
    rw [ZMod.unitsMap_def, Units.coe_map, ZMod.coe_unitOfCoprime] at h1
    simp only [MonoidHom.coe_ofClass, ZMod.castHom_apply, ZMod.cast_eq_val] at h1
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
  have hvcop : Nat.Coprime v (Q * M) := ZMod.val_coe_unit_coprime a
  -- evaluate `ψ χ_B` at `a`
  have hψ : ψ (v : ZMod Q) = 1 := by
    have h1 : v ≡ 1 [MOD Q] := (hvc.of_dvd (dvd_mul_right Q D)).trans hcQ
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr h1, Nat.cast_one, map_one]
  have hχ : jacChar B (Q * M) (fun n hn => dvd_mul_of_dvd_right (hBM n hn) Q) (v : ZMod (Q * M))
      = -1 := by
    rw [jacChar_natCast _ hvcop]
    have h1 : ∀ n ∈ B, ((jacobiSym (v : ℤ) (F n) : ℤ) : ℂ) = if n = n₀ then -1 else 1 := by
      intro n hn
      have hvF : v ≡ t n [MOD F n] :=
        ((hvc.of_dvd (dvd_mul_of_dvd_right (dvd_prod_of_mem F hn) Q)).trans (hcF n hn))
      rw [jacobi_congr hvF, ht n hn]
      split_ifs <;> simp
    rw [prod_congr rfl h1, prod_ite_eq' B n₀ (fun _ => (-1 : ℂ)), ite_eq_left hn₀]
  intro hone
  have h1 := congrArg (fun χ : DirichletCharacter ℂ (Q * M) => χ (v : ZMod (Q * M))) hone
  rw [mul_jacChar_natCast, hψ, hχ, MulChar.one_apply (by rw [hva]; exact a.isUnit)] at h1
  norm_num at h1

/-- Orthogonality: summing `ψ(a)⁻¹ ψ(p)` over the characters `ψ mod Q` picks out the
residue class `p ≡ a (mod Q)`. -/
theorem sum_filter_eq_char_sum {Q : ℕ} [NeZero Q] {a : ZMod Q} (ha : IsUnit a)
    (S : Finset ℕ) (g : ℕ → ℂ) :
    ∑ p ∈ S.filter (fun p : ℕ => (p : ZMod Q) = a), g p =
      (Q.totient : ℂ)⁻¹ * ∑ ψ : DirichletCharacter ℂ Q,
        ψ a⁻¹ * ∑ p ∈ S, ψ (p : ZMod Q) * g p := by
  classical
  have hφ : (Q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos Q)).ne'
  have hinner : ∀ p : ℕ, ∑ ψ : DirichletCharacter ℂ Q, ψ a⁻¹ * (ψ (p : ZMod Q) * g p) =
      (if a = (p : ZMod Q) then (Q.totient : ℂ) else 0) * g p := by
    intro p
    rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha (p : ZMod Q), sum_mul]
    apply sum_congr rfl
    intro ψ _
    ring
  have hR : ∑ ψ : DirichletCharacter ℂ Q, ψ a⁻¹ * ∑ p ∈ S, ψ (p : ZMod Q) * g p =
      ∑ p ∈ S, (if a = (p : ZMod Q) then (Q.totient : ℂ) else 0) * g p := by
    rw [show (∑ ψ : DirichletCharacter ℂ Q, ψ a⁻¹ * ∑ p ∈ S, ψ (p : ZMod Q) * g p) =
        ∑ ψ : DirichletCharacter ℂ Q, ∑ p ∈ S, ψ a⁻¹ * (ψ (p : ZMod Q) * g p) from
      sum_congr rfl (fun ψ _ => by rw [mul_sum])]
    rw [sum_comm]
    exact sum_congr rfl (fun p _ => hinner p)
  rw [hR, mul_sum, sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases h : (p : ZMod Q) = a
  · rw [ite_eq_left h, ite_eq_left h.symm]; field_simp
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]; simp

/-- There are `φ(Q)` Dirichlet characters modulo `Q`. -/
theorem card_dirichletCharacter (Q : ℕ) [NeZero Q] :
    (Finset.univ : Finset (DirichletCharacter ℂ Q)).card = Q.totient := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]

end ElitePrimes
