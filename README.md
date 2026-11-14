# Lean 4 formalization for "On the number of elite primes"

This repository contains the Lean 4 / mathlib formalization described in Section 7 of the
paper *On the number of elite primes* by Ali Taheri and Amir Saleh.

The formalization compiles with no `sorry` and no additional axioms. Every theorem
depends only on the three standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`). Three analytic inputs are not in mathlib; they are explicit hypotheses
(`Prop`s passed as arguments), not axioms:

| Hypothesis | Meaning | Used by |
|---|---|---|
| `BrunTitchmarsh` | Brun–Titchmarsh inequality (3), Montgomery–Vaughan form | Theorems 1.1, 1.2 |
| `GRHCharSum` | Lemma 4.1 (consequence of GRH): $\lvert\sum_{p\le x}\chi(p)\rvert \le c_0\sqrt x\log(qx)$ for non-principal $\chi \bmod q$ | Theorem 1.2 |
| `GRHPrimesInAP` | PNT in progressions under GRH: $\lvert\pi(x;q,a)-\mathrm{li}(x)/\varphi(q)\rvert \le C\sqrt x\log x$ for $1\le q\le x$ | Theorem 6.1 |

GRH itself is not stated; what is assumed is the two consequences of it that the proofs use.

## Versions

- Lean: `leanprover/lean4:v4.36.0-rc1` (pinned in `lean-toolchain`)
- mathlib: commit `957aaac3eedba59f06dde6e25469a7a0c556097c` (pinned in `lake-manifest.json`)

Do not run `lake update`: it would move mathlib to a newer commit, where some lemma names
may have changed.

## Build

Requires [elan](https://github.com/leanprover/elan).

```sh
lake exe cache get   # downloads prebuilt mathlib for the pinned commit
lake build
```

To check the axioms of every theorem (110 of them):

```sh
lake env lean CheckAxioms.lean
```

Each line should list only `[propext, Classical.choice, Quot.sound]` or a subset of it.
`CheckAxioms.lean` is generated from the `theorem` declarations in `ElitePrimes/`; to
regenerate it after adding theorems:

```sh
{ echo "import ElitePrimes"; for f in ElitePrimes/*.lean; do grep -oE "^theorem [^ ]+" "$f" | awk '{print "#print axioms ElitePrimes." $2}'; done; } > CheckAxioms.lean
```

## Correspondence with the paper

All declarations are in the namespace `ElitePrimes`. File names are historical; the
table gives the paper's numbering.

| Paper | Lean declaration | File |
|---|---|---|
| Definition of elite primes, $E(x)$ | `IsElite`, `E` | `Basic.lean`, `TheoremA.lean` |
| Lemma 2.1 (F1): Fermat numbers pairwise coprime, $\prod_{i<n}F_i = 2^{2^n}-1$ | `F_coprime`, `prod_F_range` | `Basic.lean` |
| Lemma 2.1 (F2): $r \mid F_n \Rightarrow \mathrm{ord}_r(2) = 2^{n+1}$, hence $e_r \ge n+1$ | `ord_eq_of_dvd_F`, `ev_ge_of_dvd_F` | `Structure.lean` |
| $\chi_n(3) = -1$ for $n \ge 1$ | `jacobi_three_F` | `Basic.lean` |
| Lemma 2.2: $p \nmid F_n$ for $n \ge e_p$ | `elite_not_dvd_F` | `Structure.lean` |
| Lemma 2.2: $\left(\frac{F_n}{p}\right) = -1$ for $n \ge e_p$ | `elite_jacobi_F_p` | `Structure.lean` |
| Lemma 2.2: $\left(\frac{p}{F_n}\right) = -1$ for $n \ge e_p$; $p \equiv 1 + 2^{e_p} \pmod{2^{e_p+1}}$ | `elite_jacobi_p_F`, `mod_pow_ev` | `Periodicity.lean` |
| Lemma 2.3: $\lvert\mathcal R_e\rvert \cdot 2^T = \varphi(M_e)$ for $1 \le e \le T$ (route of Remark 2.4) | `card_R_mul` | `Count.lean` |
| Brun–Titchmarsh inequality (3) (hypothesis) | `BrunTitchmarsh` | `TheoremA.lean` |
| Proposition 3.1, (4), (5), (2) at integers $N$ | `block_bound`, `big_block_bound`, `theoremA` | `TheoremA.lean` |
| Proposition 3.1, (4), (5), (2) for real $x$ with $(2^T 2^{2^T})^2 \le x$ | `block_bound_real`, `big_block_bound_real`, `theoremA_real` | `RealBounds.lean` |
| Theorem 5.1(a): $s_p \le e_p$, and $s_p < e_p$ if $e_p \ge 3$ | `sv_le_ev`, `sv_lt_ev` | `Periodicity.lean` |
| Theorem 5.1(b): for $n \ge s_p$, $F_{n+k} \equiv F_n \pmod p \iff f'_p \mid k$ (exact period $f'_p$) | `F_modEq_iff` | `Structure.lean` |
| Theorem 5.1(c), first half: $\left(\frac{F_n}{p}\right) = -1$ for $n \ge s_p$ | `elite_jacobi_of_ge_sv` | `Periodicity.lean` |
| Theorem 5.1(c), second half: $\left(\frac{1-2^{2^{s_p-1}}}{p}\right) = -1$ if $s_p \ge 1$ | `elite_extra` | `Periodicity.lean` |
| Theorem 5.1(d): $d_p = 1 \Rightarrow p \in \{3,5\}$; for elite $p \notin \{3,5\}$, $d_p > 1$ and $f'_p$ is even | `elite_dv_eq_one`, `elite_period_even`, `elite_structure_d` | `Structure.lean`, `Periodicity.lean` |
| Lemma 5.4, counting step: fewer than $D$, and at most $x/D$, odd primes $p \le x$ with $\mathrm{ord}_p(2) = D$; $\#\{p \le x : d_p = d\} \le \sum_s \min(2^s d, x/(2^s d))$ | `card_ord_eq_lt`, `card_ord_eq_le_div`, `card_dv_eq_le` | `Lemma4.lean` |
| Lemma 5.4, geometric series: $\sum_s \min(2^s d, x/(2^s d)) \le 4\sqrt x$ | `sum_min_le`, `card_dv_eq_le_sqrt` | `OddPart.lean` |
| Lemma 5.4: $\#\{p \le x : d_p \le y\} \le 2(y+1)\sqrt x$ for real $x, y \ge 0$ | `card_dv_le` (`card_dv_le_nat` at integers) | `OddPart.lean` |
| Corollary 5.5: if $d_p \le \sqrt p/(\log p)^2$ for elite $p \ge p_0$, then $E(N) \le 192\,N/(\log N)^2$ for large integers $N$ | `cor_oddpart` | `OddPart.lean` |
| Theorem 1.1, asymptotic form: $E(x) \le (16+\varepsilon)\,x\log\log x/(\log x)^2$ for large $x$ | `theoremA_asymp` | `RealBounds.lean` |
| Lemma 2.1 (F3): $\psi\chi_B$ is non-principal modulo $QM$ | `F3` (with `jacChar`, `sum_filter_eq_char_sum`) | `Characters.lean` |
| Lemma 4.1 (hypothesis) | `GRHCharSum` | `GRH.lean` |
| Proof of Theorem 1.2: bound for $N_e$; the block $e_p \ge T$; explicit inequality | `grh_block_bound`, `grh_big_block`, `theoremB_explicit` | `GRH.lean` |
| Theorem 1.2: $E(N) \le (16/3+3c_0)\,N^{3/4}(\log N)^{1/2}$ for $N \ge 2^{72}$ | `theoremB` | `GRH.lean` |
| PNT in progressions under GRH (hypothesis); $\mathrm{li}$, $M_T$, $\mathcal S_T(x)$ | `GRHPrimesInAP`, `li`, `MT`, `Sset` | `Barrier.lean` |
| Theorem 6.1, first statement: $\lvert\#\mathcal S_T(x) - \frac{T+1}{2^T}\mathrm{li}(x)\rvert \le C x^{5/6}\log x$ for $T\ge2$, $M_T \le x^{1/3}$ | `barrier_main` (with `card_Sset`, `li_lower`, `li_upper`) | `Barrier.lean` |
| Theorem 6.1, second statement: for large $x$ and $M_T \le x^{1/3} < M_{T+1}$, $\log x/12 < 2^T \le 2\log x$ and $\#\mathcal S_T(x) \asymp x\log\log x/(\log x)^2$ (constants $1/16$, $109$) | `barrier_asymp` | `Barrier.lean` |

## Not formalized

- the character-sum proof of Lemma 2.3 (Lean proves Lemma 2.3 by the route of Remark 2.4);
- the three hypotheses above themselves (Brun–Titchmarsh, and the derivation of Lemma 4.1 and
  of the PNT in progressions from GRH, which needs the explicit formula);
- the remarks, including the numerical data in Remarks 5.3 and 6.2.

## License

MIT; see [LICENSE](LICENSE).
