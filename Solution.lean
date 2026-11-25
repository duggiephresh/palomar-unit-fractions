module

public import Mathlib

/-!
# Solution: odd Znám solution and coprime Erdős #307 solution

Self-contained proof of the two `Challenge` theorems, assembled from the library at
github.com/duggiephresh/unit-fraction-solutions (`lean/Erdos307/*.lean`, concatenated in import order).
-/

@[expose] public section

-- ===== Erdos307/Forcing.lean =====

/-!
# Erdős Problem #307 — the forcing reduction

For a finite pairwise-coprime set `S` of positive integers put
`M S = ∏_{a ∈ S} a` and `A S = ∑_{a ∈ S} M S / a`.

* `coprime_A_M` / `gcd_A_M` : `gcd (A S) (M S) = 1`.
* `sum_inv_eq`, `sum_inv_num`, `sum_inv_den` : `∑ 1/a = A S / M S`, in lowest terms.
* `forcing` : `(∑_P 1/a) (∑_Q 1/b) = 1 ↔ A P = M Q ∧ A Q = M P`.
* `disjoint_of_solution` : with `1 ∉ P ∪ Q`, any solution has `P ∩ Q = ∅`.
* `prime_solution` : for sets of primes, `A P` is squarefree and `Q = (A P).primeFactors`.
* `two_cycle` : for sets of primes, a solution is exactly a 2-cycle `M P ↦ M Q ↦ M P`
  of the squarefree arithmetic derivative `sqfDeriv n = ∑_{p ∣ n} n / p`.
* `erdos_307_iff`, `coprime_one_notMem_iff` : the two open formal-conjectures statements
  (`docs/statement_307.md`) restated through the forcing reduction.
-/

namespace Erdos307

open Finset

/-- `M S = ∏_{a ∈ S} a`. -/
def M (S : Finset ℕ) : ℕ := ∏ a ∈ S, a

/-- `A S = ∑_{a ∈ S} M S / a`. -/
def A (S : Finset ℕ) : ℕ := ∑ a ∈ S, M S / a

/-- A finite set of positive, pairwise-coprime naturals. -/
def Admissible (S : Finset ℕ) : Prop :=
  (∀ a ∈ S, 0 < a) ∧ (S : Set ℕ).Pairwise Nat.Coprime

variable {S P Q : Finset ℕ}

lemma M_pos (h : ∀ a ∈ S, 0 < a) : 0 < M S := Finset.prod_pos h

lemma M_div_eq {a : ℕ} (ha : a ∈ S) (hpos : 0 < a) : M S / a = ∏ b ∈ S.erase a, b := by
  unfold M
  rw [← Finset.mul_prod_erase S (fun b => b) ha]
  exact Nat.mul_div_cancel_left _ hpos

lemma A_eq (h : ∀ a ∈ S, 0 < a) : A S = ∑ a ∈ S, ∏ b ∈ S.erase a, b := by
  unfold A
  exact Finset.sum_congr rfl fun a ha => M_div_eq ha (h a ha)

/-- `A S` is coprime to every element of `S`. -/
lemma coprime_A_mem (hS : Admissible S) {a : ℕ} (ha : a ∈ S) : Nat.Coprime (A S) a := by
  rw [A_eq hS.1, ← Finset.add_sum_erase S _ ha]
  have hdvd : a ∣ ∑ c ∈ S.erase a, ∏ b ∈ S.erase c, b := by
    refine Finset.dvd_sum fun c hc => ?_
    exact Finset.dvd_prod_of_mem (fun b => b)
      (Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hc).symm, ha⟩)
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, Nat.coprime_add_mul_left_left]
  exact Nat.Coprime.prod_left fun b hb =>
    hS.2 (Finset.mem_of_mem_erase hb) ha (Finset.ne_of_mem_erase hb)

/-- **Lowest terms:** `A S` and `M S` are coprime. -/
theorem coprime_A_M (hS : Admissible S) : Nat.Coprime (A S) (M S) :=
  Nat.Coprime.prod_right fun _ ha => coprime_A_mem hS ha

theorem gcd_A_M (hS : Admissible S) : Nat.gcd (A S) (M S) = 1 := coprime_A_M hS

/-- `∑_{a ∈ S} 1/a = A S / M S` (positivity suffices). -/
theorem sum_inv_eq (hpos : ∀ a ∈ S, 0 < a) :
    (∑ a ∈ S, (a : ℚ)⁻¹) = (A S : ℚ) / (M S : ℚ) := by
  rw [A_eq hpos, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hM : (M S : ℚ) = (a : ℚ) * ∏ b ∈ S.erase a, (b : ℚ) := by
    unfold M
    rw [Nat.cast_prod, Finset.mul_prod_erase S (fun b : ℕ => (b : ℚ)) ha]
  rw [hM, Nat.cast_prod]
  have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (hpos a ha).ne'
  have hP0 : ∏ b ∈ S.erase a, (b : ℚ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun b hb => by
      exact_mod_cast (hpos b (Finset.mem_of_mem_erase hb)).ne'
  field_simp

theorem sum_one_div_eq (hpos : ∀ a ∈ S, 0 < a) :
    (∑ a ∈ S, 1 / (a : ℚ)) = (A S : ℚ) / (M S : ℚ) := by
  simpa only [one_div] using sum_inv_eq hpos

/-- The reduced numerator of `∑ 1/a` is `A S`. -/
theorem sum_inv_num (hS : Admissible S) : (∑ a ∈ S, (a : ℚ)⁻¹).num = A S := by
  rw [sum_inv_eq hS.1]
  have hb : (0 : ℤ) < (M S : ℤ) := by exact_mod_cast M_pos hS.1
  have := Rat.num_div_eq_of_coprime (a := (A S : ℤ)) (b := (M S : ℤ)) hb
    (by simpa using coprime_A_M hS)
  simpa using this

/-- The reduced denominator of `∑ 1/a` is `M S`. -/
theorem sum_inv_den (hS : Admissible S) : (∑ a ∈ S, (a : ℚ)⁻¹).den = M S := by
  rw [sum_inv_eq hS.1]
  have hb : (0 : ℤ) < (M S : ℤ) := by exact_mod_cast M_pos hS.1
  have := Rat.den_div_eq_of_coprime (a := (A S : ℤ)) (b := (M S : ℤ)) hb
    (by simpa using coprime_A_M hS)
  exact_mod_cast (by simpa using this)

/-- **Forcing theorem.** -/
theorem forcing (hP : Admissible P) (hQ : Admissible Q) :
    (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1 ↔ A P = M Q ∧ A Q = M P := by
  rw [sum_inv_eq hP.1, sum_inv_eq hQ.1]
  have hMP : (M P : ℚ) ≠ 0 := by exact_mod_cast (M_pos hP.1).ne'
  have hMQ : (M Q : ℚ) ≠ 0 := by exact_mod_cast (M_pos hQ.1).ne'
  rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hMP hMQ)]
  norm_cast
  constructor
  · intro h
    have cP := coprime_A_M hP
    have cQ := coprime_A_M hQ
    have h1 : A P ∣ M Q := cP.dvd_of_dvd_mul_left ⟨A Q, h.symm⟩
    have h2 : M Q ∣ A P := cQ.symm.dvd_of_dvd_mul_right (h ▸ dvd_mul_left (M Q) (M P))
    have e1 : A P = M Q := Nat.dvd_antisymm h1 h2
    refine ⟨e1, ?_⟩
    rw [e1, mul_comm (M P)] at h
    exact Nat.eq_of_mul_eq_mul_left (M_pos hQ.1) h
  · rintro ⟨h1, h2⟩
    rw [h1, h2, mul_comm]

/-- Same statement in the `1 = …` orientation and `⁻¹` notation used by formal-conjectures. -/
theorem forcing' (hP : Admissible P) (hQ : Admissible Q) :
    1 = (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) ↔ A P = M Q ∧ A Q = M P := by
  rw [eq_comm]; exact forcing hP hQ

/-- With `1 ∉ P ∪ Q`, a solution has `P` and `Q` disjoint. -/
theorem disjoint_of_solution (hP : Admissible P) (hQ : Admissible Q) (h1 : 1 ∉ P ∪ Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) : Disjoint P Q := by
  rw [Finset.disjoint_left]
  intro x hxP hxQ
  have e := ((forcing hP hQ).1 heq).1
  have hx1 : x ∣ A P := e ▸ Finset.dvd_prod_of_mem (fun b => b) hxQ
  have hx2 : x ∣ M P := Finset.dvd_prod_of_mem (fun b => b) hxP
  have : x ∣ 1 := gcd_A_M hP ▸ Nat.dvd_gcd hx1 hx2
  exact h1 (Finset.mem_union_left _ (Nat.dvd_one.1 this ▸ hxP))

theorem inter_eq_empty_of_solution (hP : Admissible P) (hQ : Admissible Q) (h1 : 1 ∉ P ∪ Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) : P ∩ Q = ∅ :=
  Finset.disjoint_iff_inter_eq_empty.1 (disjoint_of_solution hP hQ h1 heq)

/-! ## Sets of primes -/

lemma admissible_of_primes (h : ∀ p ∈ S, p.Prime) : Admissible S :=
  ⟨fun p hp => (h p hp).pos, fun p hp q hq hpq => (Nat.coprime_primes (h p hp) (h q hq)).2 hpq⟩

lemma squarefree_M_of_primes (h : ∀ p ∈ S, p.Prime) : Squarefree (M S) :=
  Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.mp <|
      (Nat.coprime_primes (h p hp) (h q hq)).2 hpq)
    fun p hp => (h p hp).prime.squarefree

lemma primeFactors_M (h : ∀ p ∈ S, p.Prime) : (M S).primeFactors = S :=
  Nat.primeFactors_prod h

/-- For prime sets: `A P` is squarefree, `Q = (A P).primeFactors`, `P = (A Q).primeFactors`,
and `P ∩ Q = ∅`. -/
theorem prime_solution (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) :
    Squarefree (A P) ∧ Q = (A P).primeFactors ∧ P = (A Q).primeFactors ∧ Disjoint P Q := by
  obtain ⟨e1, e2⟩ := (forcing (admissible_of_primes hP) (admissible_of_primes hQ)).1 heq
  refine ⟨e1 ▸ squarefree_M_of_primes hQ, ?_, ?_, ?_⟩
  · rw [e1, primeFactors_M hQ]
  · rw [e2, primeFactors_M hP]
  · refine disjoint_of_solution (admissible_of_primes hP) (admissible_of_primes hQ) ?_ heq
    intro h1
    rcases Finset.mem_union.1 h1 with h | h
    · exact Nat.not_prime_one (hP 1 h)
    · exact Nat.not_prime_one (hQ 1 h)

/-- The arithmetic derivative restricted to squarefree arguments: for squarefree `n`,
`n' = ∑_{p ∣ n} n / p`. (On non-squarefree `n` this is *not* the arithmetic derivative.) -/
def sqfDeriv (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, n / p

lemma sqfDeriv_M (h : ∀ p ∈ S, p.Prime) : sqfDeriv (M S) = A S := by
  unfold sqfDeriv A
  rw [primeFactors_M h]

/-- **2-cycle equivalence.** For prime sets, `(∑_P 1/p)(∑_Q 1/q) = 1` iff the squarefree numbers
`M P`, `M Q` form a 2-cycle of the arithmetic derivative. -/
theorem two_cycle (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) :
    (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1 ↔
      sqfDeriv (M P) = M Q ∧ sqfDeriv (M Q) = M P := by
  rw [sqfDeriv_M hP, sqfDeriv_M hQ]
  exact forcing (admissible_of_primes hP) (admissible_of_primes hQ)

/-! ## The formal-conjectures statements, restated -/

/-- `erdos_307` (formal-conjectures) is equivalent to the integer system `A P = M Q, A Q = M P`
over sets of primes. -/
theorem erdos_307_iff :
    (∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧
      1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) ↔
    (∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧ A P = M Q ∧ A Q = M P) := by
  constructor
  · rintro ⟨P, Q, hP, hQ, h⟩
    exact ⟨P, Q, hP, hQ, (forcing' (admissible_of_primes hP) (admissible_of_primes hQ)).1 h⟩
  · rintro ⟨P, Q, hP, hQ, h⟩
    exact ⟨P, Q, hP, hQ, (forcing' (admissible_of_primes hP) (admissible_of_primes hQ)).2 h⟩

/-- Under the side conditions of the open variant, every element is positive. -/
lemma pos_of_variant {S : Finset ℕ} (h1 : 1 ∉ S) (hcard : 1 < S.card)
    (hcop : (S : Set ℕ).Pairwise Nat.Coprime) : ∀ a ∈ S, 0 < a := by
  intro a ha
  rcases Nat.eq_zero_or_pos a with h0 | h
  · exfalso
    subst h0
    obtain ⟨b, hb, hb0⟩ := Finset.exists_mem_ne hcard 0
    have := hcop ha hb (Ne.symm hb0)
    rw [Nat.coprime_zero_left] at this
    exact h1 (this ▸ hb)
  · exact h

/-- `erdos_307.variants.coprime_one_notMem` (formal-conjectures) restated through forcing. -/
theorem coprime_one_notMem_iff :
    (∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 ∉ P ∪ Q ∧ 1 < P.card ∧ 1 < Q.card ∧
      (P : Set ℕ).Pairwise Nat.Coprime ∧ (Q : Set ℕ).Pairwise Nat.Coprime ∧
      1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) ↔
    (∃ P Q : Finset ℕ, Admissible P ∧ Admissible Q ∧ 1 ∉ P ∪ Q ∧ 1 < P.card ∧ 1 < Q.card ∧
      A P = M Q ∧ A Q = M P) := by
  constructor
  · rintro ⟨P, Q, -, h1, hcP, hcQ, cP, cQ, h⟩
    have hP : Admissible P :=
      ⟨pos_of_variant (fun h => h1 (Finset.mem_union_left _ h)) hcP cP, cP⟩
    have hQ : Admissible Q :=
      ⟨pos_of_variant (fun h => h1 (Finset.mem_union_right _ h)) hcQ cQ, cQ⟩
    exact ⟨P, Q, hP, hQ, h1, hcP, hcQ, (forcing' hP hQ).1 h⟩
  · rintro ⟨P, Q, hP, hQ, h1, hcP, hcQ, h⟩
    refine ⟨P, Q, ?_, h1, hcP, hcQ, hP.2, hQ.2, (forcing' hP hQ).2 h⟩
    intro h0
    exact (hP.1 0 (Finset.mem_inter.1 h0).1).ne' rfl

end Erdos307

-- ===== Erdos307/Floor.lean =====

/-!
# Erdős #307 — the 59-element floor for the coprime variant (E6)

Any solution with `P`, `Q` positive, pairwise coprime and `1 ∉ P ∪ Q` has `59 ≤ #(P ∪ Q)`.

1. Forcing gives `gcd (M P) (M Q) = 1`, so `P ∪ Q` is pairwise coprime (and `P`, `Q` disjoint).
2. AM-GM: `Σ_P · Σ_Q = 1` gives `Σ_P + Σ_Q ≥ 2`.
3. `x ↦ minFac x` is injective on `P ∪ Q`, and `1/x ≤ 1/minFac x`.
4. A set `V` of at most 58 primes has `Σ_V 1/p ≤ Σ_F 1/p`, where `F` lists the 58 primes below
   277: a prime of `V \ F` is `≥ 277`, every entry of `F` is `< 277`, and `|V \ F| ≤ |F \ V|`.
5. `Σ_F 1/p < 2` (≈ 1.99874).

Only the finite facts `#F = 58`, `Σ_F 1/p < 2` and "every prime below 277 lies in `F`" are
computed; the primality of the entries of `F` is never used.
-/

namespace Erdos307

open Finset

/-- The 58 primes below 277. -/
def F58 : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
    97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
    193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271}

set_option maxRecDepth 100000 in
lemma F58_card : F58.card = 58 := by decide

set_option maxRecDepth 100000 in
lemma F58_bounds : ∀ p ∈ F58, 0 < p ∧ p < 277 := by decide

lemma F58_sum : (∑ p ∈ F58, (p : ℚ)⁻¹) < 2 := by
  simp only [F58]
  norm_num

set_option maxRecDepth 100000 in
/-- Every prime outside `F58` is at least 277. -/
lemma le_of_prime_notMem_F58 {p : ℕ} (hp : p.Prime) (h : p ∉ F58) : 277 ≤ p := by
  by_contra hlt
  push Not at hlt
  interval_cases p <;> first | exact h (by decide) | exact absurd hp (by norm_num)

/-- Comparison against any set `F` of `k` numbers in `(0, B)` containing every prime `< B`. -/
lemma sum_inv_primes_le_of {F V : Finset ℕ} {k B : ℕ} (hB : 0 < B) (hFcard : F.card = k)
    (hFb : ∀ p ∈ F, 0 < p ∧ p < B) (hFp : ∀ p, p.Prime → p ∉ F → B ≤ p)
    (hV : ∀ p ∈ V, p.Prime) (hcard : V.card ≤ k) :
    (∑ p ∈ V, (p : ℚ)⁻¹) ≤ ∑ p ∈ F, (p : ℚ)⁻¹ := by
  rw [← Finset.sum_inter_add_sum_sdiff V F, ← Finset.sum_inter_add_sum_sdiff F V,
    Finset.inter_comm F V]
  have h1 : (∑ p ∈ V \ F, (p : ℚ)⁻¹) ≤ (V \ F).card • (B : ℚ)⁻¹ := by
    refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
    obtain ⟨hpV, hpF⟩ := Finset.mem_sdiff.1 hp
    have h277 : (B : ℚ) ≤ p := by exact_mod_cast hFp p (hV p hpV) hpF
    exact inv_anti₀ (by exact_mod_cast hB) h277
  have h2 : (F \ V).card • (B : ℚ)⁻¹ ≤ ∑ p ∈ F \ V, (p : ℚ)⁻¹ := by
    refine Finset.card_nsmul_le_sum _ _ _ fun p hp => ?_
    obtain ⟨hpos, hlt⟩ := hFb p (Finset.mem_sdiff.1 hp).1
    exact inv_anti₀ (by exact_mod_cast hpos) (by exact_mod_cast hlt.le)
  have hc : (V \ F).card ≤ (F \ V).card := by
    have a := Finset.card_sdiff_add_card_inter V F
    have b := Finset.card_sdiff_add_card_inter F V
    rw [Finset.inter_comm, hFcard] at b
    omega
  have h3 : (V \ F).card • (B : ℚ)⁻¹ ≤ (F \ V).card • (B : ℚ)⁻¹ := by
    rw [nsmul_eq_mul, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
  linarith

/-- At most 58 primes have reciprocal sum at most that of the 58 primes below 277. -/
lemma sum_inv_primes_le {V : Finset ℕ} (hV : ∀ p ∈ V, p.Prime) (hcard : V.card ≤ 58) :
    (∑ p ∈ V, (p : ℚ)⁻¹) ≤ ∑ p ∈ F58, (p : ℚ)⁻¹ :=
  sum_inv_primes_le_of (by norm_num) F58_card F58_bounds (fun _ hp h => le_of_prime_notMem_F58 hp h) hV hcard

/-- On a pairwise-coprime set of integers `> 1`, `minFac` is injective onto primes and
`1/x ≤ 1/minFac x`. -/
lemma sum_inv_le_minFac {U : Finset ℕ} (hgt : ∀ x ∈ U, 1 < x)
    (hcop : (U : Set ℕ).Pairwise Nat.Coprime) :
    (∑ x ∈ U, (x : ℚ)⁻¹) ≤ ∑ p ∈ U.image Nat.minFac, (p : ℚ)⁻¹ ∧
      (U.image Nat.minFac).card = U.card ∧ ∀ p ∈ U.image Nat.minFac, p.Prime := by
  have hinj : Set.InjOn Nat.minFac (U : Set ℕ) := by
    intro x hx y hy hxy
    by_contra hne
    have c := hcop hx hy hne
    have hdx : x.minFac ∣ x := Nat.minFac_dvd x
    have hdy : x.minFac ∣ y := hxy ▸ Nat.minFac_dvd y
    have h1 : x.minFac ∣ 1 := c ▸ Nat.dvd_gcd hdx hdy
    have : x = 1 := Nat.minFac_eq_one_iff.1 (Nat.dvd_one.1 h1)
    exact absurd (hgt x hx) (by omega)
  refine ⟨?_, Finset.card_image_of_injOn hinj, ?_⟩
  · rw [Finset.sum_image hinj]
    refine Finset.sum_le_sum fun x hx => ?_
    have hx0 : 0 < x := by have := hgt x hx; omega
    exact inv_anti₀ (by exact_mod_cast Nat.minFac_pos x)
      (by exact_mod_cast Nat.minFac_le hx0)
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
    exact Nat.minFac_prime (by have := hgt x hx; omega)

/-- In a solution, elements of `P` and `Q` are coprime. -/
lemma cross_coprime {P Q : Finset ℕ} (hP : Admissible P) (hQ : Admissible Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) {a b : ℕ} (ha : a ∈ P)
    (hb : b ∈ Q) : Nat.Coprime a b := by
  have e := ((forcing hP hQ).1 heq).1
  have c : Nat.Coprime (M P) (M Q) := e ▸ (coprime_A_M hP).symm
  exact Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun x => x) hb)
    (Nat.Coprime.coprime_dvd_left (Finset.dvd_prod_of_mem (fun x => x) ha) c)

/-- AM-GM for a product equal to one. -/
lemma two_le_add_of_mul_eq_one {s t : ℚ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s * t = 1) :
    2 ≤ s + t := by
  nlinarith [sq_nonneg (s - t)]

/-- **E6: the floor.** Any solution of the coprime variant with `1 ∉ P ∪ Q` uses at least
59 numbers. -/
theorem card_floor {P Q : Finset ℕ} (hP : Admissible P) (hQ : Admissible Q) (h1 : 1 ∉ P ∪ Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) : 59 ≤ (P ∪ Q).card := by
  by_contra hlt
  push Not at hlt
  have hgt : ∀ x ∈ P ∪ Q, 1 < x := by
    intro x hx
    have hpos : 0 < x := by
      rcases Finset.mem_union.1 hx with h | h
      · exact hP.1 x h
      · exact hQ.1 x h
    have hne : x ≠ 1 := fun e => h1 (e ▸ hx)
    omega
  have hcop : ((P ∪ Q : Finset ℕ) : Set ℕ).Pairwise Nat.Coprime := by
    intro x hx y hy hne
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hP.2 hx hy hne
    · exact cross_coprime hP hQ heq hx hy
    · exact (cross_coprime hP hQ heq hy hx).symm
    · exact hQ.2 hx hy hne
  obtain ⟨hle, hcard, hprime⟩ := sum_inv_le_minFac hgt hcop
  have hV := sum_inv_primes_le hprime (by omega)
  have hsum : (∑ x ∈ P ∪ Q, (x : ℚ)⁻¹) = (∑ a ∈ P, (a : ℚ)⁻¹) + ∑ b ∈ Q, (b : ℚ)⁻¹ :=
    Finset.sum_union (disjoint_of_solution hP hQ h1 heq)
  have hamgm := two_le_add_of_mul_eq_one
    (Finset.sum_nonneg fun a _ => inv_nonneg.2 (Nat.cast_nonneg a))
    (Finset.sum_nonneg fun b _ => inv_nonneg.2 (Nat.cast_nonneg b)) heq
  linarith [F58_sum]

/-- The floor in the exact form of formal-conjectures' `erdos_307.variants.coprime_one_notMem`
hypotheses. -/
theorem coprime_one_notMem_card_floor {P Q : Finset ℕ} (h1 : 1 ∉ P ∪ Q) (hcP : 1 < P.card)
    (hcQ : 1 < Q.card) (cP : (P : Set ℕ).Pairwise Nat.Coprime)
    (cQ : (Q : Set ℕ).Pairwise Nat.Coprime)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) : 59 ≤ (P ∪ Q).card :=
  card_floor ⟨pos_of_variant (fun h => h1 (Finset.mem_union_left _ h)) hcP cP, cP⟩
    ⟨pos_of_variant (fun h => h1 (Finset.mem_union_right _ h)) hcQ cQ, cQ⟩ h1 heq.symm

/-- Cross-check: the same argument gives the 59-prime half of the upstream `erdos_307.barrier`
(Bonfioli), with no `Q.Nonempty` hypothesis. -/
theorem prime_card_floor {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) : 59 ≤ (P ∪ Q).card := by
  refine card_floor (admissible_of_primes hP) (admissible_of_primes hQ) ?_ heq.symm
  intro h
  rcases Finset.mem_union.1 h with h | h
  · exact Nat.not_prime_one (hP 1 h)
  · exact Nat.not_prime_one (hQ 1 h)

end Erdos307

-- ===== Erdos307/Square.lean =====

/-!
# Erdős #307 — the square criterion and the closing lemma (E7)

* `A_union` : for disjoint positive `P`, `Q` : `A (P ∪ Q) = A P * M Q + A Q * M P`.
* `square_criterion` : in a solution with `P`, `Q` disjoint,
  `A (P ∪ Q) = M P ^ 2 + M Q ^ 2` and `M (P ∪ Q) = M P * M Q`; hence (`square_pm`)
  `A U + 2 M U = (M P + M Q)²` and `A U − 2 M U = (M P − M Q)²`.
* `prime_square` : for prime sets, `n = ∏ (P ∪ Q)` has `n' + 2n` and `n' − 2n` both squares
  (`n'` the arithmetic derivative, `sqfDeriv`).
* `closing` : if `P0`, `Q0` are admissible, cross-coprime and `M Q0 · M P0 = A Q0 · A P0 + 1`,
  then `P0 ∪ {M Q0² + A Q0 · M P0}` and `Q0 ∪ {M Q0 · A P0 + M P0²}` solve the equation, with
  everything pairwise coprime. `coprime_one_notMem_of_closing` : such a pair with
  `1 ∉ P0 ∪ Q0`, both nonempty, proves the open variant `erdos_307.variants.coprime_one_notMem`.
-/

namespace Erdos307

open Finset

variable {P Q : Finset ℕ}

lemma M_union (h : Disjoint P Q) : M (P ∪ Q) = M P * M Q := Finset.prod_union h

lemma pos_union (hP : ∀ a ∈ P, 0 < a) (hQ : ∀ b ∈ Q, 0 < b) : ∀ x ∈ P ∪ Q, 0 < x := by
  intro x hx
  rcases Finset.mem_union.1 hx with h | h
  · exact hP x h
  · exact hQ x h

lemma A_union (hP : ∀ a ∈ P, 0 < a) (hQ : ∀ b ∈ Q, 0 < b) (h : Disjoint P Q) :
    A (P ∪ Q) = A P * M Q + A Q * M P := by
  have e := sum_inv_eq (pos_union hP hQ)
  rw [Finset.sum_union h, sum_inv_eq hP, sum_inv_eq hQ, M_union h] at e
  have hMP : (M P : ℚ) ≠ 0 := by exact_mod_cast (M_pos hP).ne'
  have hMQ : (M Q : ℚ) ≠ 0 := by exact_mod_cast (M_pos hQ).ne'
  have key : (A (P ∪ Q) : ℚ) = A P * M Q + A Q * M P := by
    rw [Nat.cast_mul] at e
    field_simp at e
    linarith
  exact_mod_cast key

/-- **Square criterion.** -/
theorem square_criterion (hP : Admissible P) (hQ : Admissible Q) (hd : Disjoint P Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) :
    A (P ∪ Q) = M P ^ 2 + M Q ^ 2 ∧ M (P ∪ Q) = M P * M Q := by
  obtain ⟨e1, e2⟩ := (forcing hP hQ).1 heq
  refine ⟨?_, M_union hd⟩
  rw [A_union hP.1 hQ.1 hd, e1, e2]
  ring

theorem square_pm (hP : Admissible P) (hQ : Admissible Q) (hd : Disjoint P Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) :
    A (P ∪ Q) + 2 * M (P ∪ Q) = (M P + M Q) ^ 2 ∧
      (A (P ∪ Q) : ℤ) - 2 * M (P ∪ Q) = ((M P : ℤ) - M Q) ^ 2 := by
  obtain ⟨h1, h2⟩ := square_criterion hP hQ hd heq
  refine ⟨by rw [h1, h2]; ring, ?_⟩
  rw [h1, h2]
  push_cast
  ring

/-- For the open variant (`1 ∉ P ∪ Q`) disjointness is automatic. -/
theorem square_pm_of_one_notMem (hP : Admissible P) (hQ : Admissible Q) (h1 : 1 ∉ P ∪ Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) :
    IsSquare (A (P ∪ Q) + 2 * M (P ∪ Q)) ∧ IsSquare ((A (P ∪ Q) : ℤ) - 2 * M (P ∪ Q)) := by
  obtain ⟨h1', h2'⟩ := square_pm hP hQ (disjoint_of_solution hP hQ h1 heq) heq
  exact ⟨⟨M P + M Q, by rw [h1']; ring⟩, ⟨(M P : ℤ) - M Q, by rw [h2']; ring⟩⟩

/-- **Prime form:** for a solution in primes and `n = ∏ (P ∪ Q)`, both `n' + 2n` and `n' − 2n` are
perfect squares, `n'` the arithmetic derivative. -/
theorem prime_square (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) :
    IsSquare (sqfDeriv (M (P ∪ Q)) + 2 * M (P ∪ Q)) ∧
      IsSquare ((sqfDeriv (M (P ∪ Q)) : ℤ) - 2 * M (P ∪ Q)) := by
  have hU : ∀ x ∈ P ∪ Q, x.Prime := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact hP x h
    · exact hQ x h
  rw [sqfDeriv_M hU]
  refine square_pm_of_one_notMem (admissible_of_primes hP) (admissible_of_primes hQ) ?_ heq
  intro h
  exact Nat.not_prime_one (hU 1 h)

/-! ## The closing lemma -/

section closing

variable {P0 Q0 : Finset ℕ}

/-- **Closing lemma.** A pair with `M Q0 · M P0 = A Q0 · A P0 + 1` closes to a solution. -/
theorem closing (hP : Admissible P0) (hQ : Admissible Q0)
    (hcross : ∀ a ∈ P0, ∀ b ∈ Q0, Nat.Coprime a b) (hQne : Q0.Nonempty) (hPne : P0.Nonempty)
    (h1 : 1 ∉ P0 ∪ Q0) (hD : M Q0 * M P0 = A Q0 * A P0 + 1) :
    Admissible (insert (M Q0 ^ 2 + A Q0 * M P0) P0) ∧
    Admissible (insert (M Q0 * A P0 + M P0 ^ 2) Q0) ∧
    (M Q0 ^ 2 + A Q0 * M P0) ∉ P0 ∧ (M Q0 * A P0 + M P0 ^ 2) ∉ Q0 ∧
    (∀ x ∈ insert (M Q0 ^ 2 + A Q0 * M P0) P0, ∀ y ∈ insert (M Q0 * A P0 + M P0 ^ 2) Q0,
      Nat.Coprime x y) ∧
    (∑ x ∈ insert (M Q0 ^ 2 + A Q0 * M P0) P0, (x : ℚ)⁻¹) *
      (∑ y ∈ insert (M Q0 * A P0 + M P0 ^ 2) Q0, (y : ℚ)⁻¹) = 1 := by
  set MP := M P0 with hMPdef
  set AP := A P0 with hAPdef
  set MQ := M Q0 with hMQdef
  set AQ := A Q0 with hAQdef
  set a := MQ ^ 2 + AQ * MP with ha
  set b := MQ * AP + MP ^ 2 with hb
  -- basic coprimality
  have cPQ : Nat.Coprime MP MQ :=
    Nat.Coprime.prod_left fun x hx => Nat.Coprime.prod_right fun y hy => hcross x hx y hy
  have cAP : Nat.Coprime AP MP := coprime_A_M hP
  have cAQ : Nat.Coprime AQ MQ := coprime_A_M hQ
  have ha_MP : Nat.Coprime a MP := by
    rw [ha, Nat.coprime_add_mul_right_left]
    exact Nat.Coprime.pow_left 2 cPQ.symm
  have ha_MQ : Nat.Coprime a MQ := by
    have : a = AQ * MP + MQ * MQ := by rw [ha]; ring
    rw [this, Nat.coprime_add_mul_left_left]
    exact Nat.Coprime.mul_left cAQ cPQ
  have hb_MQ : Nat.Coprime b MQ := by
    have : b = MP ^ 2 + AP * MQ := by rw [hb]; ring
    rw [this, Nat.coprime_add_mul_right_left]
    exact Nat.Coprime.pow_left 2 cPQ
  have hb_MP : Nat.Coprime b MP := by
    have : b = MQ * AP + MP * MP := by rw [hb]; ring
    rw [this, Nat.coprime_add_mul_left_left]
    exact Nat.Coprime.mul_left cPQ.symm cAP
  -- the two linear relations, from hD
  have hDz : (MQ : ℤ) * MP = AQ * AP + 1 := by exact_mod_cast hD
  have E1 : MQ * b = MP + AP * a := by
    have : (MQ : ℤ) * b = MP + AP * a := by
      rw [hb, ha]; push_cast; linear_combination (MP : ℤ) * hDz
    exact_mod_cast this
  have E2 : MP * a = MQ + AQ * b := by
    have : (MP : ℤ) * a = MQ + AQ * b := by
      rw [hb, ha]; push_cast; linear_combination (MQ : ℤ) * hDz
    exact_mod_cast this
  have hab : Nat.Coprime a b := by
    have h' : Nat.Coprime (MP + AP * a) a := by
      rw [Nat.coprime_add_mul_right_left]; exact ha_MP.symm
    rw [← E1] at h'
    exact Nat.Coprime.coprime_mul_left_right h'.symm
  -- sizes
  have hMQ2 : 2 ≤ MQ := by
    obtain ⟨y, hy⟩ := hQne
    have hy1 : y ≠ 1 := fun e => h1 (Finset.mem_union_right _ (e ▸ hy))
    have hy0 := hQ.1 y hy
    have : y ≤ MQ := Nat.le_of_dvd (M_pos hQ.1) (Finset.dvd_prod_of_mem (fun x => x) hy)
    omega
  have hMP2 : 2 ≤ MP := by
    obtain ⟨y, hy⟩ := hPne
    have hy1 : y ≠ 1 := fun e => h1 (Finset.mem_union_left _ (e ▸ hy))
    have hy0 := hP.1 y hy
    have : y ≤ MP := Nat.le_of_dvd (M_pos hP.1) (Finset.dvd_prod_of_mem (fun x => x) hy)
    omega
  have ha2 : 2 ≤ a := by rw [ha]; nlinarith
  have hb2 : 2 ≤ b := by rw [hb]; nlinarith
  have haP : a ∉ P0 := by
    intro h
    have := Nat.Coprime.eq_one_of_dvd ha_MP (Finset.dvd_prod_of_mem (fun x => x) h)
    omega
  have hbQ : b ∉ Q0 := by
    intro h
    have := Nat.Coprime.eq_one_of_dvd hb_MQ (Finset.dvd_prod_of_mem (fun x => x) h)
    omega
  -- admissibility
  have adP : Admissible (insert a P0) := by
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases Finset.mem_insert.1 hx with rfl | h
      · omega
      · exact hP.1 x h
    · rw [Finset.coe_insert, Set.pairwise_insert]
      refine ⟨hP.2, fun y hy _ => ?_⟩
      have c : Nat.Coprime a y :=
        Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun x => x) hy) ha_MP
      exact ⟨c, c.symm⟩
  have adQ : Admissible (insert b Q0) := by
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases Finset.mem_insert.1 hx with rfl | h
      · omega
      · exact hQ.1 x h
    · rw [Finset.coe_insert, Set.pairwise_insert]
      refine ⟨hQ.2, fun y hy _ => ?_⟩
      have c : Nat.Coprime b y :=
        Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun x => x) hy) hb_MQ
      exact ⟨c, c.symm⟩
  refine ⟨adP, adQ, haP, hbQ, ?_, ?_⟩
  · intro x hx y hy
    rcases Finset.mem_insert.1 hx with rfl | hx <;> rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hab
    · exact Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun x => x) hy) ha_MQ
    · exact (Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun x => x) hx) hb_MP).symm
    · exact hcross x hx y hy
  · rw [Finset.sum_insert haP, Finset.sum_insert hbQ, sum_inv_eq hP.1, sum_inv_eq hQ.1]
    have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
    have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
    have hP0 : (MP : ℚ) ≠ 0 := by exact_mod_cast (show MP ≠ 0 by omega)
    have hQ0 : (MQ : ℚ) ≠ 0 := by exact_mod_cast (show MQ ≠ 0 by omega)
    have E1q : (MQ : ℚ) * b = MP + AP * a := by exact_mod_cast E1
    have E2q : (MP : ℚ) * a = MQ + AQ * b := by exact_mod_cast E2
    have s1 : (a : ℚ)⁻¹ + AP / MP = (MQ * b) / (a * MP) := by
      rw [E1q]; field_simp
    have s2 : (b : ℚ)⁻¹ + AQ / MQ = (MP * a) / (b * MQ) := by
      rw [E2q]; field_simp
    rw [s1, s2]
    field_simp

/-- **Sufficient condition for the open variant.** A cross-coprime admissible pair `P0`, `Q0`,
both nonempty, without `1`, with `M Q0 · M P0 = A Q0 · A P0 + 1`, proves
`erdos_307.variants.coprime_one_notMem` (stated exactly as in formal-conjectures). -/
theorem coprime_one_notMem_of_closing (hP : Admissible P0) (hQ : Admissible Q0)
    (hcross : ∀ a ∈ P0, ∀ b ∈ Q0, Nat.Coprime a b) (hQne : Q0.Nonempty) (hPne : P0.Nonempty)
    (h1 : 1 ∉ P0 ∪ Q0) (hD : M Q0 * M P0 = A Q0 * A P0 + 1) :
    ∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 ∉ P ∪ Q ∧ 1 < P.card ∧ 1 < Q.card ∧
      (P : Set ℕ).Pairwise Nat.Coprime ∧ (Q : Set ℕ).Pairwise Nat.Coprime ∧
      1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) := by
  obtain ⟨adP, adQ, haP, hbQ, -, heq⟩ := closing hP hQ hcross hQne hPne h1 hD
  refine ⟨_, _, ?_, ?_, ?_, ?_, adP.2, adQ.2, heq.symm⟩
  · intro h0
    exact (adP.1 0 (Finset.mem_inter.1 h0).1).ne' rfl
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_insert.1 h with e | h
      · -- the new element `a` is ≥ 2
        have : 2 ≤ M Q0 ^ 2 + A Q0 * M P0 := by
          obtain ⟨y, hy⟩ := hQne
          have hy1 : y ≠ 1 := fun e => h1 (Finset.mem_union_right _ (e ▸ hy))
          have : y ≤ M Q0 :=
            Nat.le_of_dvd (M_pos hQ.1) (Finset.dvd_prod_of_mem (fun x => x) hy)
          have hy2 : 2 ≤ y := by have := hQ.1 y hy; omega
          nlinarith
        omega
      · exact h1 (Finset.mem_union_left _ h)
    · rcases Finset.mem_insert.1 h with e | h
      · have : 2 ≤ M Q0 * A P0 + M P0 ^ 2 := by
          obtain ⟨y, hy⟩ := hPne
          have hy1 : y ≠ 1 := fun e => h1 (Finset.mem_union_left _ (e ▸ hy))
          have : y ≤ M P0 :=
            Nat.le_of_dvd (M_pos hP.1) (Finset.dvd_prod_of_mem (fun x => x) hy)
          have hy2 : 2 ≤ y := by have := hP.1 y hy; omega
          nlinarith
        omega
      · exact h1 (Finset.mem_union_right _ h)
  · rw [Finset.card_insert_of_notMem haP]
    have := Finset.card_pos.2 hPne
    omega
  · rw [Finset.card_insert_of_notMem hbQ]
    have := Finset.card_pos.2 hQne
    omega

end closing

end Erdos307

-- ===== Erdos307/Descent.lean =====

/-!
# Erdős #307, coprime variant: existence conditional on a descent hypothesis

Write `Dev P Q = M(Q)·M(P) − A(Q)·A(P)` (an integer). By the closing lemma (`Square.lean`), an
admissible, cross-coprime pair with `Dev = 1` and no `1` closes to a solution of the open variant
`erdos_307.variants.coprime_one_notMem`.

`DescentHyp` says: every such "good" state with `Dev > 1` extends, by appending two new pairwise
coprime elements `x, y > 1` (coprime to everything present) to `P`, to a state with
`0 < Dev′ < Dev`. Gemini's two-element hyperbola descent (sprint lens R3-E) predicts such
extensions, even with `Dev′ < Dev / 2`, with an expected count that grows at every step; proving it
is an open thin-strip equidistribution problem.

Proved here (standard axioms):
- the descent machinery: `dev_insert2` (step formula), `dev_mul_dev_insert2` (the strip identity
  `Dev·Dev′ = (Dev·x − E)(Dev·y − E) − E²`, `E = A(Q)·M(P)`), `good_extend` (good states are
  closed under coprime extension), and `closes_of_dev_one`;
- `coprime_one_notMem_of_descent` and `coprime_one_notMem_of_descentBelow` (descent ⇒ the open variant).

**Honest status of the hypotheses (2026-11-24).**
- `DescentHyp` is FALSE (`not_descentHyp`, proved), so the first theorem is vacuous.
- `DescentHypBelow K` restricts to near-solution states. It is not known to be false, but it is
  universal over infinitely many states, while the halving heuristic gives each state a failure
  chance of about q0^(−c²/2) > 0. Ford-type exceptional sets make the universal form *heuristically
  false*. The heuristic supports only "some descent path survives" (a branching-process statement),
  which no ∀-state hypothesis captures.
- `DescentHypDeep M₀` (Gemini's refinement; the main result `coprime_one_notMem_of_descentDeep`)
  addresses both problems:
  - it adds `Coprime (M P) (A Q)`, which removes the local obstruction `dvd_dev_of_dvd`;
  - it requires `Dev² ≤ M(P)M(Q)`, so the halving start point is `q₀ ≥ √M`;
  - it allows **arbitrary finite** extensions `S`.

  Heuristically (Gemini, reported; not re-checked by Claude) the number of descending extensions
  per state grows fast enough that a union bound over all deep states converges, so the universal
  hypothesis is *plausible* under a Poisson model. Ford-type correlations are not ruled out.
  **It is a conjecture, not a theorem.**
- A deep seed exists: `scripts/deep_seed.py` builds one, with 69 elements, log₁₀ Dev = 115.5 and
  log₁₀ M(P)M(Q) = 4595.4. It is verified with exact integers in Python, not yet in Lean.
- Net: a genuine conditional reduction of the open variant to `DescentHypDeep`, a natural
  thin-strip / equidistribution conjecture, with the vacuous versions proved false and the local
  obstruction explicit.
-/

namespace Erdos307

open Finset

/-- The closing-lemma deviation `M(Q)·M(P) − A(Q)·A(P)`. -/
def Dev (P Q : Finset ℕ) : ℤ := (M Q : ℤ) * M P - (A Q : ℤ) * A P

/-- A state from which the closing lemma / descent can proceed. -/
def Good (P Q : Finset ℕ) : Prop :=
  Admissible P ∧ Admissible Q ∧ (∀ a ∈ P, ∀ b ∈ Q, Nat.Coprime a b) ∧ P.Nonempty ∧
    Q.Nonempty ∧ 1 ∉ P ∪ Q ∧ 0 < Dev P Q

/-- **Descent hypothesis.** Every good state with `Dev > 1` admits a two-element extension of `P`
by new coprime elements that strictly lowers the (still positive) deviation. -/
def DescentHyp : Prop :=
  ∀ P Q : Finset ℕ, Good P Q → 1 < Dev P Q →
    ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x ≠ y ∧ Nat.Coprime x (M P * M Q) ∧
      Nat.Coprime y (M P * M Q) ∧ Nat.Coprime x y ∧
      0 < Dev (insert x (insert y P)) Q ∧ Dev (insert x (insert y P)) Q < Dev P Q

lemma M_insert {S : Finset ℕ} {x : ℕ} (hxS : x ∉ S) : M (insert x S) = x * M S := by
  unfold M
  rw [Finset.prod_insert hxS]

lemma A_insert {S : Finset ℕ} {x : ℕ} (hS : ∀ a ∈ S, 0 < a) (hx : 0 < x) (hxS : x ∉ S) :
    A (insert x S) = x * A S + M S := by
  have hpos : ∀ a ∈ insert x S, 0 < a := by
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | h
    · exact hx
    · exact hS a h
  have e := sum_inv_eq hpos
  rw [Finset.sum_insert hxS, sum_inv_eq hS, M_insert hxS] at e
  have hMS : (M S : ℚ) ≠ 0 := by exact_mod_cast (M_pos hS).ne'
  have hx0 : (x : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
  have key : (A (insert x S) : ℚ) = x * A S + M S := by
    rw [Nat.cast_mul] at e
    field_simp at e
    linarith
  exact_mod_cast key

/-- The deviation after appending two new elements to `P`. -/
lemma dev_insert2 {P Q : Finset ℕ} {x y : ℕ} (hP : ∀ a ∈ P, 0 < a) (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≠ y) (hxP : x ∉ P) (hyP : y ∉ P) :
    Dev (insert x (insert y P)) Q =
      (x : ℤ) * y * Dev P Q - ((A Q : ℤ) * M P) * ((x : ℤ) + y) := by
  have hyP' : ∀ a ∈ insert y P, 0 < a := by
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | h
    · exact hy
    · exact hP a h
  have hxyP : x ∉ insert y P := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hxy, hxP⟩
  unfold Dev
  rw [A_insert hyP' hx hxyP, M_insert hxyP, A_insert hP hy hyP, M_insert hyP]
  push_cast
  ring

/-- The thin-strip identity behind the halving mechanism:
`Dev·Dev′ = (Dev·x − E)(Dev·y − E) − E²` with `E = A(Q)·M(P)`. -/
lemma dev_mul_dev_insert2 {P Q : Finset ℕ} {x y : ℕ} (hP : ∀ a ∈ P, 0 < a) (hx : 0 < x)
    (hy : 0 < y) (hxy : x ≠ y) (hxP : x ∉ P) (hyP : y ∉ P) :
    Dev P Q * Dev (insert x (insert y P)) Q =
      (Dev P Q * x - (A Q : ℤ) * M P) * (Dev P Q * y - (A Q : ℤ) * M P) -
        ((A Q : ℤ) * M P) ^ 2 := by
  rw [dev_insert2 hP hx hy hxy hxP hyP]
  ring

lemma not_mem_of_coprime_M {S : Finset ℕ} {x : ℕ} (hx1 : 1 < x) (h : Nat.Coprime x (M S)) :
    x ∉ S := by
  intro hx
  have := Nat.Coprime.eq_one_of_dvd h (Finset.dvd_prod_of_mem (fun a => a) hx)
  omega

lemma coprime_of_mem_of_coprime_M {S : Finset ℕ} {x a : ℕ} (ha : a ∈ S)
    (h : Nat.Coprime x (M S)) : Nat.Coprime x a :=
  Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun b => b) ha) h

/-- A two-element extension of a good state by new coprime elements is good again. -/
lemma good_extend {P Q : Finset ℕ} {x y : ℕ} (hG : Good P Q) (hx1 : 1 < x) (hy1 : 1 < y)
    (hxy : x ≠ y) (hxM : Nat.Coprime x (M P * M Q)) (hyM : Nat.Coprime y (M P * M Q))
    (hcxy : Nat.Coprime x y) (hpos : 0 < Dev (insert x (insert y P)) Q) :
    Good (insert x (insert y P)) Q := by
  obtain ⟨hP, hQ, hc, hPne, hQne, h1, -⟩ := hG
  have hxP : Nat.Coprime x (M P) := Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hxM
  have hxQ : Nat.Coprime x (M Q) := Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) hxM
  have hyP : Nat.Coprime y (M P) := Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hyM
  have hyQ : Nat.Coprime y (M Q) := Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) hyM
  refine ⟨⟨?_, ?_⟩, hQ, ?_, ⟨x, Finset.mem_insert_self _ _⟩, hQne, ?_, hpos⟩
  · intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · omega
    rcases Finset.mem_insert.1 ha with rfl | ha
    · omega
    · exact hP.1 a ha
  · rw [Finset.coe_insert, Finset.coe_insert, Set.pairwise_insert, Set.pairwise_insert]
    refine ⟨⟨hP.2, fun b hb _ => ?_⟩, fun b hb hne => ?_⟩
    · have c := coprime_of_mem_of_coprime_M hb hyP
      exact ⟨c, c.symm⟩
    · rcases hb with rfl | hb
      · exact ⟨hcxy, hcxy.symm⟩
      · have c := coprime_of_mem_of_coprime_M hb hxP
        exact ⟨c, c.symm⟩
  · intro a ha b hb
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact coprime_of_mem_of_coprime_M hb hxQ
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact coprime_of_mem_of_coprime_M hb hyQ
    · exact hc a ha b hb
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_insert.1 h with e | h
      · omega
      rcases Finset.mem_insert.1 h with e | h
      · omega
      · exact h1 (Finset.mem_union_left _ h)
    · exact h1 (Finset.mem_union_right _ h)

/-- The open variant, exactly as stated in formal-conjectures (`coprime_one_notMem`). -/
def CoprimeOneNotMem : Prop :=
  ∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 ∉ P ∪ Q ∧ 1 < P.card ∧ 1 < Q.card ∧
    (P : Set ℕ).Pairwise Nat.Coprime ∧ (Q : Set ℕ).Pairwise Nat.Coprime ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)

lemma closes_of_dev_one {P Q : Finset ℕ} (hG : Good P Q) (h1 : Dev P Q = 1) :
    CoprimeOneNotMem := by
  obtain ⟨hP, hQ, hc, hPne, hQne, hone, -⟩ := hG
  have hD : M Q * M P = A Q * A P + 1 := by
    unfold Dev at h1
    have : ((M Q * M P : ℕ) : ℤ) = ((A Q * A P + 1 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  exact coprime_one_notMem_of_closing hP hQ hc hQne hPne hone hD

/-- The starting state `({2}, {3})`, with `Dev = 3·2 − 1·1 = 5`. -/
lemma good_two_three : Good {2} {3} := by
  refine ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩, ?_, by simp, by simp, by simp, ?_⟩
  · intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst ha; subst hb
    decide
  · simp [Dev, M, A]

/-- **Main theorem.** The descent hypothesis implies the open coprime / 1-excluded variant of
Erdős #307. -/
theorem coprime_one_notMem_of_descent (H : DescentHyp) : CoprimeOneNotMem := by
  have key : ∀ n : ℕ, ∀ P Q : Finset ℕ, Good P Q → Dev P Q = n → CoprimeOneNotMem := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P Q hG hn
      by_cases hn1 : n = 1
      · exact closes_of_dev_one hG (by rw [hn, hn1]; norm_num)
      · have hD := hG.2.2.2.2.2.2
        have hgt : 1 < Dev P Q := by rw [hn] at hD ⊢; omega
        obtain ⟨x, y, hx1, hy1, hxy, hxM, hyM, hcxy, hpos, hlt⟩ := H P Q hG hgt
        have hG' := good_extend hG hx1 hy1 hxy hxM hyM hcxy hpos
        have hnat := Int.toNat_of_nonneg hpos.le
        refine ih (Dev (insert x (insert y P)) Q).toNat ?_ _ Q hG' hnat.symm
        omega
  exact key _ {2} {3} good_two_three (Int.toNat_of_nonneg good_two_three.2.2.2.2.2.2.le).symm

/-- **Sanity check: the unrestricted `DescentHyp` is FALSE**, so `coprime_one_notMem_of_descent`
is vacuous. At `({2}, {3})` (`Dev = 5`), new elements must be coprime to 6, so they are ≥ 5 and
`Dev′ = 5xy − 2(x + y) ≥ 105`. The halving mechanism only operates near a solution; see
`DescentHypBelow`. -/
theorem not_descentHyp : ¬ DescentHyp := by
  intro H
  have hgt : 1 < Dev {2} {3} := by simp [Dev, M, A]
  obtain ⟨x, y, hx1, hy1, hxy, hxM, hyM, -, -, hlt⟩ := H {2} {3} good_two_three hgt
  have hxP : x ∉ ({2} : Finset ℕ) := not_mem_of_coprime_M hx1
    (Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hxM)
  have hyP : y ∉ ({2} : Finset ℕ) := not_mem_of_coprime_M hy1
    (Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hyM)
  rw [dev_insert2 (by simp) (by omega) (by omega) hxy hxP hyP] at hlt
  have h5 : Dev {2} {3} = 5 := by simp [Dev, M, A]
  have hA : (A {3} : ℤ) * M {2} = 2 := by simp [M, A]
  rw [h5, hA] at hlt
  have hx2 : (2 : ℤ) ≤ x := by exact_mod_cast hx1
  have hy2 : (2 : ℤ) ≤ y := by exact_mod_cast hy1
  nlinarith

/-- **Near-solution descent hypothesis.** Restricted to good states with deviation ratio
`Dev / (M(P)·M(Q)) ≤ 1/K`, a class closed under the descent step (`Dev′ < Dev` while the
products grow). This is where Gemini's halving mechanism lives. -/
def DescentHypBelow (K : ℕ) : Prop :=
  ∀ P Q : Finset ℕ, Good P Q → 1 < Dev P Q → Dev P Q * K ≤ (M P : ℤ) * M Q →
    ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x ≠ y ∧ Nat.Coprime x (M P * M Q) ∧
      Nat.Coprime y (M P * M Q) ∧ Nat.Coprime x y ∧
      0 < Dev (insert x (insert y P)) Q ∧ Dev (insert x (insert y P)) Q < Dev P Q

/-- **Conditional existence (non-vacuous form).** If some good state lies in the near-solution
class `Dev·K ≤ M(P)M(Q)`, and every state of that class descends, then the open coprime variant
of Erdős #307 holds. -/
theorem coprime_one_notMem_of_descentBelow (K : ℕ) (H : DescentHypBelow K)
    (P0 Q0 : Finset ℕ) (hG0 : Good P0 Q0) (hK0 : Dev P0 Q0 * K ≤ (M P0 : ℤ) * M Q0) :
    CoprimeOneNotMem := by
  have key : ∀ n : ℕ, ∀ P Q : Finset ℕ, Good P Q → Dev P Q * K ≤ (M P : ℤ) * M Q →
      Dev P Q = n → CoprimeOneNotMem := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P Q hG hK hn
      by_cases hn1 : n = 1
      · exact closes_of_dev_one hG (by rw [hn, hn1]; norm_num)
      · have hD := hG.2.2.2.2.2.2
        have hgt : 1 < Dev P Q := by rw [hn] at hD ⊢; omega
        obtain ⟨x, y, hx1, hy1, hxy, hxM, hyM, hcxy, hpos, hlt⟩ := H P Q hG hgt hK
        have hG' := good_extend hG hx1 hy1 hxy hxM hyM hcxy hpos
        -- the class is closed: Dev′·K < Dev·K ≤ M(P)M(Q) ≤ M(P′)M(Q)
        have hxP : x ∉ P := not_mem_of_coprime_M hx1
          (Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hxM)
        have hyP : y ∉ P := not_mem_of_coprime_M hy1
          (Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hyM)
        have hxyP : x ∉ insert y P := by
          simp only [Finset.mem_insert, not_or]; exact ⟨hxy, hxP⟩
        have hM' : M (insert x (insert y P)) = x * (y * M P) := by
          rw [M_insert hxyP, M_insert hyP]
        have hMP : 0 < M P := M_pos hG.1.1
        have hMQ : 0 < M Q := M_pos hG.2.1.1
        have hgrow : (M P : ℤ) * M Q ≤ (M (insert x (insert y P)) : ℤ) * M Q := by
          rw [hM']
          have h1 : (M P : ℤ) ≤ (x : ℤ) * (y * M P) := by
            have : (1 : ℤ) ≤ (x : ℤ) * y := by
              have hx' : (1 : ℤ) ≤ x := by exact_mod_cast hx1.le
              have hy' : (1 : ℤ) ≤ y := by exact_mod_cast hy1.le
              nlinarith
            have hm : (0 : ℤ) ≤ M P := by exact_mod_cast hMP.le
            nlinarith
          push_cast
          exact mul_le_mul_of_nonneg_right h1 (by exact_mod_cast hMQ.le)
        have hK' : Dev (insert x (insert y P)) Q * K ≤
            (M (insert x (insert y P)) : ℤ) * M Q := by
          have hk : (0 : ℤ) ≤ K := by exact_mod_cast Nat.zero_le K
          nlinarith
        have hnat := Int.toNat_of_nonneg hpos.le
        refine ih (Dev (insert x (insert y P)) Q).toNat ?_ _ Q hG' hK' hnat.symm
        omega
  exact key _ P0 Q0 hG0 hK0 (Int.toNat_of_nonneg hG0.2.2.2.2.2.2.le).symm

/-! ## The `Deep` class (Gemini's refinement) and arbitrary finite extensions -/

/-- **Local obstruction (Gemini, 2026-11-24).** If a prime `p` divides both `M(P)` and `A(Q)`, it
divides `Dev` for every extension of `P`, so one-sided descent can never reach `Dev = 1`. `Deep`
therefore requires `Coprime (M P) (A Q)`. -/
lemma dvd_dev_of_dvd {P Q : Finset ℕ} {p : ℕ} (hP : p ∣ M P) (hQ : p ∣ A Q) :
    (p : ℤ) ∣ Dev P Q := by
  unfold Dev
  exact dvd_sub (Dvd.dvd.mul_left (by exact_mod_cast hP) _)
    (Dvd.dvd.mul_right (by exact_mod_cast hQ) _)

/-- Deep near-solution states: good, `σ(Q) ≥ 1`, no local obstruction, large, and
`Dev² ≤ M(P)M(Q)`, so the halving start point `q₀ ≥ √M`. Closed under descent. -/
def Deep (M₀ : ℕ) (P Q : Finset ℕ) : Prop :=
  Good P Q ∧ M Q ≤ A Q ∧ Nat.Coprime (M P) (A Q) ∧ M₀ ≤ M P * M Q ∧
    Dev P Q ^ 2 ≤ (M P : ℤ) * M Q

/-- **Deep descent hypothesis.** Every deep state with `Dev > 1` admits a finite extension `S` of
`P` by new elements, pairwise coprime and coprime to `M(P)·M(Q)·A(Q)`, that lowers the
(positive) deviation. Gemini's two- and three-element halving pairs are special cases.
Heuristic support (Gemini, reported, not checked by Claude): with arbitrary finite `S`, the expected
number of descending extensions grows fast enough that a union bound over all deep states
converges (Poisson model); Ford-type correlations are not ruled out. -/
def DescentHypDeep (M₀ : ℕ) : Prop :=
  ∀ P Q : Finset ℕ, Deep M₀ P Q → 1 < Dev P Q →
    ∃ S : Finset ℕ, (∀ s ∈ S, 1 < s ∧ Nat.Coprime s (M P * M Q * A Q)) ∧
      (S : Set ℕ).Pairwise Nat.Coprime ∧ 0 < Dev (P ∪ S) Q ∧ Dev (P ∪ S) Q < Dev P Q

lemma deep_extend {M₀ : ℕ} {P Q S : Finset ℕ} (hD : Deep M₀ P Q)
    (hS : ∀ s ∈ S, 1 < s ∧ Nat.Coprime s (M P * M Q * A Q))
    (hSc : (S : Set ℕ).Pairwise Nat.Coprime) (hpos : 0 < Dev (P ∪ S) Q)
    (hlt : Dev (P ∪ S) Q < Dev P Q) : Deep M₀ (P ∪ S) Q := by
  obtain ⟨⟨hP, hQ, hc, hPne, hQne, h1, hDpos⟩, hMQ, hcop, hM0, hsq⟩ := hD
  have hsP : ∀ s ∈ S, Nat.Coprime s (M P) := fun s hs =>
    Nat.Coprime.coprime_dvd_right (Dvd.intro (M Q * A Q) (by ring)) (hS s hs).2
  have hsQ : ∀ s ∈ S, Nat.Coprime s (M Q) := fun s hs =>
    Nat.Coprime.coprime_dvd_right (Dvd.intro (M P * A Q) (by ring)) (hS s hs).2
  have hsA : ∀ s ∈ S, Nat.Coprime s (A Q) := fun s hs =>
    Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) (hS s hs).2
  have hdisj : Disjoint P S := by
    rw [Finset.disjoint_left]
    intro a haP haS
    have := Nat.Coprime.eq_one_of_dvd (hsP a haS) (Finset.dvd_prod_of_mem (fun b => b) haP)
    have := (hS a haS).1
    omega
  have hMU : M (P ∪ S) = M P * M S := Finset.prod_union hdisj
  have hMS : 0 < M S := Finset.prod_pos fun s hs => by have := (hS s hs).1; omega
  have hMP : 0 < M P := M_pos hP.1
  have hMQpos : 0 < M Q := M_pos hQ.1
  have hgrow : M P * M Q ≤ M (P ∪ S) * M Q := by
    rw [hMU]; exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hMS)
  refine ⟨⟨⟨fun a ha => ?_, ?_⟩, hQ, ?_, ?_, hQne, ?_, hpos⟩, hMQ, ?_, ?_, ?_⟩
  · rcases Finset.mem_union.1 ha with h | h
    · exact hP.1 a h
    · have := (hS a h).1; omega
  · intro a ha b hb hab
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hP.2 ha hb hab
    · exact (coprime_of_mem_of_coprime_M ha (hsP b hb)).symm
    · exact coprime_of_mem_of_coprime_M hb (hsP a ha)
    · exact hSc ha hb hab
  · intro a ha b hb
    rcases Finset.mem_union.1 ha with h | h
    · exact hc a h b hb
    · exact coprime_of_mem_of_coprime_M hb (hsQ a h)
  · obtain ⟨a, ha⟩ := hPne; exact ⟨a, Finset.mem_union_left _ ha⟩
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_union.1 h with h | h
      · exact h1 (Finset.mem_union_left _ h)
      · have := (hS 1 h).1; omega
    · exact h1 (Finset.mem_union_right _ h)
  · rw [hMU]
    exact Nat.Coprime.mul_left hcop (Nat.Coprime.prod_left fun s hs => hsA s hs)
  · exact le_trans hM0 hgrow
  · have h0 : (0 : ℤ) < Dev (P ∪ S) Q := hpos
    have hsq' : Dev (P ∪ S) Q ^ 2 < Dev P Q ^ 2 := by nlinarith
    have : ((M P * M Q : ℕ) : ℤ) ≤ ((M (P ∪ S) * M Q : ℕ) : ℤ) := by exact_mod_cast hgrow
    push_cast at this
    linarith

/-- **Conditional existence (Deep form).** If the deep descent hypothesis holds at level `M₀`, and
some deep state exists at that level, the open coprime / 1-excluded variant of Erdős #307 holds. -/
theorem coprime_one_notMem_of_descentDeep (M₀ : ℕ) (H : DescentHypDeep M₀)
    (P0 Q0 : Finset ℕ) (h0 : Deep M₀ P0 Q0) : CoprimeOneNotMem := by
  have key : ∀ n : ℕ, ∀ P Q : Finset ℕ, Deep M₀ P Q → Dev P Q = n → CoprimeOneNotMem := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P Q hD hn
      by_cases hn1 : n = 1
      · exact closes_of_dev_one hD.1 (by rw [hn, hn1]; norm_num)
      · have hDp := hD.1.2.2.2.2.2.2
        have hgt : 1 < Dev P Q := by rw [hn] at hDp ⊢; omega
        obtain ⟨S, hS, hSc, hpos, hlt⟩ := H P Q hD hgt
        have hD' := deep_extend hD hS hSc hpos hlt
        have hnat := Int.toNat_of_nonneg hpos.le
        refine ih (Dev (P ∪ S) Q).toNat ?_ _ Q hD' hnat.symm
        omega
  exact key _ P0 Q0 h0 (Int.toNat_of_nonneg h0.1.2.2.2.2.2.2.le).symm

/-! ## Egyptian-fraction reformulation -/

/-- **Extension formula.** For a disjoint positive extension `S` of `P`:
`Dev(P ∪ S, Q) = M(S)·Dev(P, Q) − E·A(S)` with `E = A(Q)·M(P)`. So descent is the statement
`σ(S) ∈ (t − t/M(S), t)` with `t = Dev/E`: an Egyptian underapproximation of `t` with relative
error below `1/∏S` (`σ(S) = t` exactly would be a solution of #307). -/
lemma dev_union {P Q S : Finset ℕ} (hP : ∀ a ∈ P, 0 < a) (hS : ∀ s ∈ S, 0 < s)
    (hd : Disjoint P S) :
    Dev (P ∪ S) Q = (M S : ℤ) * Dev P Q - ((A Q : ℤ) * M P) * A S := by
  unfold Dev
  rw [A_union hP hS hd, M_union hd]
  push_cast
  ring

/-- The descent hypothesis in Egyptian-fraction form (same conclusion, stated through
`M(S)·Dev − E·A(S)`); it implies `DescentHypDeep`. -/
def EgyptHypDeep (M₀ : ℕ) : Prop :=
  ∀ P Q : Finset ℕ, Deep M₀ P Q → 1 < Dev P Q →
    ∃ S : Finset ℕ, (∀ s ∈ S, 1 < s ∧ Nat.Coprime s (M P * M Q * A Q)) ∧
      (S : Set ℕ).Pairwise Nat.Coprime ∧
      0 < (M S : ℤ) * Dev P Q - ((A Q : ℤ) * M P) * A S ∧
      (M S : ℤ) * Dev P Q - ((A Q : ℤ) * M P) * A S < Dev P Q

theorem descentHypDeep_of_egypt {M₀ : ℕ} (H : EgyptHypDeep M₀) : DescentHypDeep M₀ := by
  intro P Q hD hgt
  obtain ⟨S, hS, hSc, h1, h2⟩ := H P Q hD hgt
  refine ⟨S, hS, hSc, ?_, ?_⟩ <;>
  · have hdisj : Disjoint P S := by
      rw [Finset.disjoint_left]
      intro a haP haS
      have hc : Nat.Coprime a (M P) := Nat.Coprime.coprime_dvd_right
        (Dvd.intro (M Q * A Q) (by ring)) (hS a haS).2
      have := Nat.Coprime.eq_one_of_dvd hc (Finset.dvd_prod_of_mem (fun b => b) haP)
      have := (hS a haS).1
      omega
    rwa [dev_union hD.1.1.1 (fun s hs => by have := (hS s hs).1; omega) hdisj]

/-! ## A proved special case: the greedy element -/

/-- In a deep state, `Dev` and `E = A(Q)·M(P)` share no prime factor. -/
lemma not_dvd_dev_and_E {M₀ : ℕ} {P Q : Finset ℕ} (hD : Deep M₀ P Q) {p : ℕ} (hp : p.Prime)
    (h1 : (p : ℤ) ∣ Dev P Q) (h2 : p ∣ A Q * M P) : False := by
  obtain ⟨⟨hP, hQ, -, -, -, -, -⟩, -, hcop, -, -⟩ := hD
  have cAP := coprime_A_M hP
  have cAQ := coprime_A_M hQ
  have bad : ∀ {a b : ℕ}, Nat.Coprime a b → p ∣ a → p ∣ b → False := fun hab ha hb => by
    have : p ∣ Nat.gcd _ _ := Nat.dvd_gcd ha hb
    rw [hab] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  unfold Dev at h1
  rcases (Nat.Prime.dvd_mul hp).1 h2 with hA | hM
  · -- p ∣ A Q ⇒ p ∣ M Q · M P
    have : (p : ℤ) ∣ (M Q : ℤ) * M P := by
      have hAA : (p : ℤ) ∣ (A Q : ℤ) * A P := Dvd.dvd.mul_right (by exact_mod_cast hA) _
      have := dvd_add h1 hAA
      simpa using this
    have : p ∣ M Q * M P := by exact_mod_cast this
    rcases (Nat.Prime.dvd_mul hp).1 this with h | h
    · exact bad cAQ hA h
    · exact bad hcop h hA
  · -- p ∣ M P ⇒ p ∣ A Q · A P
    have : (p : ℤ) ∣ (A Q : ℤ) * A P := by
      have hMM : (p : ℤ) ∣ (M Q : ℤ) * M P := Dvd.dvd.mul_left (by exact_mod_cast hM) _
      have := dvd_sub hMM h1
      simpa using this
    have : p ∣ A Q * A P := by exact_mod_cast this
    rcases (Nat.Prime.dvd_mul hp).1 this with h | h
    · exact bad hcop hM h
    · exact bad cAP h hM

/-- **Greedy descent (proved).** In a deep state with `Dev > 1`, if the greedy element
`s = ⌊E/Dev⌋ + 1` (`E = A(Q)·M(P)`) is `> 1` and coprime to `M(P)·M(Q)·A(Q)`, then `S = {s}`
descends: `Dev′ = Dev − (E mod Dev) ∈ (0, Dev)`. -/
theorem greedy_descends {M₀ : ℕ} {P Q : Finset ℕ} (hD : Deep M₀ P Q) (hgt : 1 < Dev P Q)
    (hs1 : 1 < A Q * M P / (Dev P Q).toNat + 1)
    (hsc : Nat.Coprime (A Q * M P / (Dev P Q).toNat + 1) (M P * M Q * A Q)) :
    ∃ S : Finset ℕ, (∀ s ∈ S, 1 < s ∧ Nat.Coprime s (M P * M Q * A Q)) ∧
      (S : Set ℕ).Pairwise Nat.Coprime ∧ 0 < Dev (P ∪ S) Q ∧ Dev (P ∪ S) Q < Dev P Q := by
  obtain ⟨d, hdD⟩ : ∃ d : ℕ, (d : ℤ) = Dev P Q := ⟨(Dev P Q).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hdt : (Dev P Q).toNat = d := by rw [← hdD]; simp
  rw [hdt] at hs1 hsc
  have hd1 : 1 < d := by omega
  -- d does not divide E = A(Q)·M(P) (coprime, d > 1)
  have hmod : A Q * M P % d ≠ 0 := by
    intro h0
    have hdvd : d ∣ A Q * M P := Nat.dvd_of_mod_eq_zero h0
    have hp := Nat.minFac_prime (show d ≠ 1 by omega)
    exact not_dvd_dev_and_E hD hp (by rw [← hdD]; exact_mod_cast Nat.minFac_dvd d)
      ((Nat.minFac_dvd d).trans hdvd)
  have hlt : A Q * M P % d < d := Nat.mod_lt _ (by omega)
  have hdiv := Nat.div_add_mod (A Q * M P) d
  have hsP : A Q * M P / d + 1 ∉ P := by
    intro hm
    have hc : Nat.Coprime (A Q * M P / d + 1) (M P) := Nat.Coprime.coprime_dvd_right
      (Dvd.intro (M Q * A Q) (by ring)) hsc
    have := Nat.Coprime.eq_one_of_dvd hc (Finset.dvd_prod_of_mem (fun b => b) hm)
    omega
  have hdisj : Disjoint P {A Q * M P / d + 1} := Finset.disjoint_singleton_right.2 hsP
  have hform := dev_union (Q := Q) hD.1.1.1
    (fun t ht => by rw [Finset.mem_singleton.1 ht]; omega) hdisj
  have hMs : M {A Q * M P / d + 1} = A Q * M P / d + 1 := by simp [M]
  have hAs : A {A Q * M P / d + 1} = 1 := by simp [A, M]
  rw [hMs, hAs] at hform
  have key : Dev (P ∪ {A Q * M P / d + 1}) Q = (d : ℤ) - ((A Q * M P % d : ℕ) : ℤ) := by
    rw [hform, ← hdD]
    have h' : ((A Q * M P : ℕ) : ℤ) =
        (d : ℤ) * ((A Q * M P / d : ℕ) : ℤ) + ((A Q * M P % d : ℕ) : ℤ) := by
      exact_mod_cast hdiv.symm
    push_cast at h' ⊢
    linear_combination (-1 : ℤ) * h'
  have hr : 0 < A Q * M P % d := Nat.pos_of_ne_zero hmod
  refine ⟨{A Q * M P / d + 1}, ?_, by simp, ?_, ?_⟩
  · intro t ht
    rw [Finset.mem_singleton.1 ht]
    exact ⟨hs1, hsc⟩
  · rw [key]; omega
  · rw [key, ← hdD]; omega

/-- So the hypothesis only needs assuming at **hard** states, where the greedy element is not
admissible. -/
def EgyptHypHard (M₀ : ℕ) : Prop :=
  ∀ P Q : Finset ℕ, Deep M₀ P Q → 1 < Dev P Q →
    ¬ (1 < A Q * M P / (Dev P Q).toNat + 1 ∧
      Nat.Coprime (A Q * M P / (Dev P Q).toNat + 1) (M P * M Q * A Q)) →
    ∃ S : Finset ℕ, (∀ s ∈ S, 1 < s ∧ Nat.Coprime s (M P * M Q * A Q)) ∧
      (S : Set ℕ).Pairwise Nat.Coprime ∧ 0 < Dev (P ∪ S) Q ∧ Dev (P ∪ S) Q < Dev P Q

theorem descentHypDeep_of_hard {M₀ : ℕ} (H : EgyptHypHard M₀) : DescentHypDeep M₀ := by
  intro P Q hD hgt
  by_cases hg : 1 < A Q * M P / (Dev P Q).toNat + 1 ∧
      Nat.Coprime (A Q * M P / (Dev P Q).toNat + 1) (M P * M Q * A Q)
  · exact greedy_descends hD hgt hg.1 hg.2
  · exact H P Q hD hgt hg

/-- **Headline.** The open coprime / 1-excluded variant of Erdős #307 follows from the descent
hypothesis at *hard* deep states only (those whose greedy element is not admissible), given one
deep seed. Easy states are handled unconditionally by `greedy_descends`. -/
theorem coprime_one_notMem_of_hard (M₀ : ℕ) (H : EgyptHypHard M₀) (P0 Q0 : Finset ℕ)
    (h0 : Deep M₀ P0 Q0) : CoprimeOneNotMem :=
  coprime_one_notMem_of_descentDeep M₀ (descentHypDeep_of_hard H) P0 Q0 h0

/-- Gemini's halving form (`Dev′ < Dev/2`) is a special case of the descent hypothesis. -/
theorem descentHyp_of_halving
    (H : ∀ P Q : Finset ℕ, Good P Q → 1 < Dev P Q →
      ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x ≠ y ∧ Nat.Coprime x (M P * M Q) ∧
        Nat.Coprime y (M P * M Q) ∧ Nat.Coprime x y ∧
        0 < Dev (insert x (insert y P)) Q ∧ 2 * Dev (insert x (insert y P)) Q < Dev P Q) :
    DescentHyp := by
  intro P Q hG hgt
  obtain ⟨x, y, h1, h2, h3, h4, h5, h6, h7, h8⟩ := H P Q hG hgt
  exact ⟨x, y, h1, h2, h3, h4, h5, h6, h7, by linarith⟩

end Erdos307

-- ===== Erdos307/ImplicitChain.lean =====

/-!
# Kernel check of implicit descent chains (Claude, 2026-11-25)

A chain is given by `Q`, a seed `P₀` and deviations `d₀, d₁, …, dₙ`. The elements are
`sⱼ = (Eⱼ + dⱼ₊₁)/dⱼ` with `E₀ = A(Q)·M(P₀)` and `Eⱼ₊₁ = Eⱼ·sⱼ`. They are never computed: a Bool checker
works with residues only, and `chain_sound` turns a `true` answer into the hypotheses of `closing`.

* `implicit_step`: one step preserves admissibility, cross-coprimality and `1 ∉ P`, and moves `Dev` from
  `d` to `d'`.
* `stepCheck`, `stepCheck_sound`: the residue checker and its soundness.
-/

namespace Erdos307

open Finset

/-- **One implicit step.** If `s·d = E + d'` with `E = A(Q)·M(P)`, `d'` coprime to `E`, `s` coprime to
every element of `Q` and `s > 1`, then `insert s P` is again admissible, cross-coprime with `Q`, free
of `1`, and has deviation `d'`. -/
theorem implicit_step {P Q : Finset ℕ} {d d' s : ℕ}
    (hP : Admissible P) (hcross : ∀ a ∈ P, ∀ b ∈ Q, Nat.Coprime a b) (h1 : 1 ∉ P)
    (hdev : Dev P Q = d)
    (hs : s * d = A Q * M P + d') (hcop : Nat.Coprime d' (A Q * M P))
    (hsQ : ∀ q ∈ Q, Nat.Coprime s q) (hs1 : 1 < s) :
    s ∉ P ∧ Admissible (insert s P) ∧ (∀ a ∈ insert s P, ∀ b ∈ Q, Nat.Coprime a b) ∧
      1 ∉ insert s P ∧ Dev (insert s P) Q = d' ∧ A Q * M (insert s P) = (A Q * M P) * s := by
  set E := A Q * M P with hE
  -- s is coprime to E: a common prime would divide s·d − E = d'
  have hsE : Nat.Coprime s E := by
    apply Nat.coprime_of_dvd
    intro l hl hls hlE
    have h1' : l ∣ E + d' := hs ▸ Dvd.dvd.mul_right hls d
    have hld' : l ∣ d' := (Nat.dvd_add_right hlE).mp h1'
    have : l ∣ Nat.gcd d' E := Nat.dvd_gcd hld' hlE
    rw [hcop] at this
    exact hl.one_lt.ne' (Nat.dvd_one.mp this)
  have hMdvd : ∀ p ∈ P, p ∣ E := fun p hp =>
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hp) _
  have hsP : s ∉ P := by
    intro hsP
    have : Nat.gcd s E = s := Nat.gcd_eq_left (hMdvd s hsP)
    rw [hsE] at this
    omega
  refine ⟨hsP, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · omega
    · exact hP.1 a ha
  · rw [Finset.coe_insert]
    refine Set.Pairwise.insert hP.2 fun p hp _ => ?_
    have hc : Nat.Coprime s p := Nat.Coprime.coprime_dvd_right (hMdvd p hp) hsE
    exact ⟨hc, hc.symm⟩
  · intro a ha b hb
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hsQ b hb
    · exact hcross a ha b hb
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · omega
    · exact h1 h
  · have hS : ∀ x ∈ ({s} : Finset ℕ), 0 < x := by
      intro x hx; rw [Finset.mem_singleton] at hx; omega
    have hdisj : Disjoint P {s} := Finset.disjoint_singleton_right.mpr hsP
    have hform := dev_union (Q := Q) hP.1 hS hdisj
    have hMs : M ({s} : Finset ℕ) = s := by simp [M]
    have hAs : A ({s} : Finset ℕ) = 1 := by
      simp only [A, hMs, Finset.sum_singleton]; exact Nat.div_self (by omega)
    rw [show insert s P = P ∪ {s} by rw [Finset.insert_eq, Finset.union_comm], hform, hMs, hAs, hdev]
    have : ((s * d : ℕ) : ℤ) = ((E + d' : ℕ) : ℤ) := by rw [hs]
    push_cast at this
    simp only [hE] at this ⊢
    push_cast
    linarith
  · rw [M, Finset.prod_insert hsP]
    simp only [hE, M]
    ring

/-- Cap for the running lower bound on `E` (any value ≥ 2·max dⱼ works). -/
def capLB : ℕ := 10 ^ 200

/-- **The residue checker.** `R` is the current modulus, `Em` the residue of the implicit `E`, `lb` a lower
bound for `E`, `d` the current deviation; the list holds the remaining deviations. -/
def stepCheck (qs : List ℕ) : ℕ → ℕ → ℕ → ℕ → List ℕ → Bool
  | _, _, _, d, [] => d == 1
  | R, Em, lb, d, d' :: rest =>
    ((Em + d') % d == 0) && (Nat.gcd (Em % d') d' == 1) && (d' != 0) &&
      qs.all (fun q => Nat.gcd ((((Em + d') % R) / d) % q) q == 1) && Nat.ble (2 * d) (lb + d') &&
      stepCheck qs (R / d) ((Em % (R / d)) * (((Em + d') % R) / d) % (R / d))
        (min capLB (lb * ((lb + d') / d))) d' rest

/-- **Soundness of the residue checker.** -/
theorem stepCheck_sound {Q : Finset ℕ} {qs : List ℕ} (hqs : ∀ q ∈ Q, q ∈ qs) :
    ∀ (rest : List ℕ) (P : Finset ℕ) (d R Em lb : ℕ),
      Admissible P → (∀ a ∈ P, ∀ b ∈ Q, Nat.Coprime a b) → 1 ∉ P → P.Nonempty →
      Dev P Q = d → 0 < d → R = M Q * (d :: rest).prod → Em ≡ A Q * M P [MOD R] →
      lb ≤ A Q * M P → stepCheck qs R Em lb d rest = true →
      ∃ P' : Finset ℕ, Admissible P' ∧ (∀ a ∈ P', ∀ b ∈ Q, Nat.Coprime a b) ∧ 1 ∉ P' ∧
        P'.Nonempty ∧ Dev P' Q = 1 := by
  intro rest
  induction rest with
  | nil =>
    intro P d R Em lb hP hcross h1 hne hdev _ _ _ _ hchk
    simp only [stepCheck, beq_iff_eq] at hchk
    exact ⟨P, hP, hcross, h1, hne, by rw [hdev, hchk]; rfl⟩
  | cons d' rest ih =>
    intro P d R Em lb hP hcross h1 hne hdev hd hR hEm hlb hchk
    simp only [stepCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true,
      Nat.ble_eq] at hchk
    obtain ⟨⟨⟨⟨⟨hi, hii⟩, hd'0⟩, hiii⟩, hiv⟩, hnext⟩ := hchk
    set E := A Q * M P with hE
    set Rn := M Q * (d' :: rest).prod with hRn
    have hRdRn : R = d * Rn := by rw [hR, hRn, List.prod_cons]; ring
    have hRdiv : R / d = Rn := by rw [hRdRn, Nat.mul_div_cancel_left _ hd]
    have hdR : d ∣ R := ⟨Rn, hRdRn⟩
    have hRnR : Rn ∣ R := ⟨d, by rw [hRdRn]; ring⟩
    have hd'R : d' ∣ R := by
      rw [hRdRn, hRn, List.prod_cons]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_right d' _) _) _
    -- (i) integrality
    have hEmd : Em ≡ E [MOD d] := Nat.ModEq.of_dvd hdR hEm
    have hdiv : d ∣ E + d' := by
      apply Nat.dvd_of_mod_eq_zero
      have := (hEmd.add_right d').symm
      unfold Nat.ModEq at this; rw [this]; exact hi
    set s := (E + d') / d with hsdef
    have hs : s * d = E + d' := Nat.div_mul_cancel hdiv
    -- (ii) coprimality with E
    have hcop : Nat.Coprime d' E := by
      have h' : Em % d' = E % d' := Nat.ModEq.of_dvd hd'R hEm
      rw [h'] at hii
      unfold Nat.Coprime; rw [Nat.gcd_rec]; exact hii
    -- s modulo Rn
    have hsm : ((Em + d') % R) / d ≡ s [MOD Rn] := by
      have ht : (Em + d') % R ≡ E + d' [MOD R] := (Nat.mod_modEq _ _).trans (hEm.add_right d')
      have htd : d ∣ (Em + d') % R := by
        apply Nat.dvd_of_mod_eq_zero
        have := Nat.ModEq.of_dvd hdR ht
        unfold Nat.ModEq at this; rw [this]; exact Nat.mod_eq_zero_of_dvd hdiv
      have e1 : (Em + d') % R = d * (((Em + d') % R) / d) := (Nat.mul_div_cancel' htd).symm
      have e2 : E + d' = d * s := by rw [mul_comm]; exact hs.symm
      rw [e1, e2] at ht
      rw [hRdRn] at ht ⊢
      exact Nat.ModEq.mul_left_cancel' (c := d) (by omega) ht
    -- (iii) s coprime to Q
    have hsQ : ∀ q ∈ Q, Nat.Coprime s q := by
      intro q hq
      have hqRn : q ∣ Rn := Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ hq) _
      have h3 := hiii q (hqs q hq)
      have h' : (((Em + d') % R) / d) % q = s % q := Nat.ModEq.of_dvd hqRn hsm
      rw [h'] at h3
      have : Nat.gcd q s = 1 := by rw [Nat.gcd_rec]; exact h3
      exact Nat.Coprime.symm this
    -- (iv) s > 1
    have hs1 : 1 < s := by
      have h2 : 2 * d ≤ E + d' := le_trans hiv (by omega)
      rw [← hs] at h2
      have : 2 ≤ s := Nat.le_of_mul_le_mul_right (by rw [mul_comm] at h2; linarith [h2]) hd
      omega
    obtain ⟨hsP, hP', hcross', h1', hdev', hE'⟩ :=
      implicit_step hP hcross h1 hdev hs hcop hsQ hs1
    refine ih (insert s P) d' Rn ((Em % Rn) * (((Em + d') % R) / d) % Rn)
      (min capLB (lb * ((lb + d') / d))) hP' hcross' h1' (Finset.insert_nonempty _ _) hdev'
      (by omega) hRn ?_ ?_ ?_
    · rw [hE']
      have hEmRn : Em % Rn ≡ E [MOD Rn] := (Nat.mod_modEq _ _).trans (Nat.ModEq.of_dvd hRnR hEm)
      exact (Nat.mod_modEq _ _).trans (hEmRn.mul hsm)
    · rw [hE']
      refine le_trans (min_le_right _ _) (Nat.mul_le_mul hlb ?_)
      exact Nat.div_le_div_right (by omega)
    · rw [hRdiv] at hnext; exact hnext

/-- **From a passing check to the open statement.** -/
theorem coprime_one_notMem_of_stepCheck {Q P0 : Finset ℕ} {qs : List ℕ} (hqs : ∀ q ∈ Q, q ∈ qs)
    (hQ : Admissible Q) (hQne : Q.Nonempty) (h1Q : 1 ∉ Q)
    (hP0 : Admissible P0) (hcross : ∀ a ∈ P0, ∀ b ∈ Q, Nat.Coprime a b) (h1P : 1 ∉ P0)
    (hP0ne : P0.Nonempty) {d0 : ℕ} (hdev : Dev P0 Q = d0) (hd0 : 0 < d0) (rest : List ℕ)
    (hchk : stepCheck qs (M Q * (d0 :: rest).prod) ((A Q * M P0) % (M Q * (d0 :: rest).prod))
      (A Q * M P0) d0 rest = true) : CoprimeOneNotMem := by
  obtain ⟨P, hP, hc, h1, hne, hdev1⟩ := stepCheck_sound hqs rest P0 d0 _ _ _ hP0 hcross h1P hP0ne
    hdev hd0 rfl (Nat.mod_modEq _ _) le_rfl hchk
  refine closes_of_dev_one ⟨hP, hQ, hc, hne, hQne, ?_, by rw [hdev1]; norm_num⟩ hdev1
  intro h
  rcases Finset.mem_union.mp h with h | h
  · exact h1 h
  · exact h1Q h

end Erdos307

-- ===== Erdos307/CoprimeSolution.lean =====
/-!
# Kernel-checked certificate: a solution of the coprime, 1-excluded variant of Erdős #307

Certificate `erdos307-coprime/certificate.txt` (sha256 ecb1397a93bd72bd3ecc628416c6225fcb34c4f2a080579c45f59c4014473119),
found by a residue-only beam descent (Fable session, 2026-11-25). The deviations below define 913 implicit
elements; the kernel runs `stepCheck` on them, and `coprime_one_notMem_of_stepCheck` concludes.
-/
namespace Erdos307

set_option maxRecDepth 1000000
def solQ : List ℕ := [2, 3, 7, 41]
def solP0 : List ℕ := [5, 11, 13, 17, 19, 23, 29, 31, 37, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271]
def solD0 : ℕ := 399317102181519648748531027788408430645554284720114800883959866918778551945838634066041627720822282576341734
def solRest : List ℕ := [
  291315515032578698547627281349027580188918159068555993733480972770382438888049618962413739555302424865009698377,
  155739097602172039423328334888486273907861355444896092898947255568659847618647263904221080210522788711474915574,
  60868962831075758074997787551184262051560784739233579950184806884133103711739045665653548511020048212967043,
  29665721728531691195632533803920577900115642959339981753906110258875984862068500828272374220927514479406716934,
  3832913704332285662784221895296087342015877180994326681629985217582282334524964819097862276174383942955617,
  214721035420708383343768027523517867334520326587161393543076088854370777210005444122126255015410693449696865024,
  62888689099488841821676100515743207301012358137041007789621849200955824521441630228938780341007422155871,
  395675869305603355333915946579281394657161325335523789766627715004026686208113238822312728562020863020803338,
  4028070703028965276034018103317493017314973093188565806550455174983025864396673001518628359555564867789669,
  22544004482827607956405162579754146171449000402867438945941159414553936902162243850307406719912497480792802,
  1151812493813150083532608916405371584846990160769693839880805435283132096173561264657777168341359886793271783,
  55342192405685314967477090123311330543642148615855030903399808907601770777674077202866159344283198669618,
  96755996166846631016476125113102350375205687756074098590394643296849267559364562046443637458682576788867021,
  6129772801106899429908731162719384104834857532488082704532550539202974941488001947967709598959950349940102,
  7820405325634027196043681425949398246055545624904628590794948189544962681451214089452565063296338380104763,
  1237941239094119440920445255196948988229783508476283483176643337507119537818742436356286573286664542342412,
  60146982777909211203009871566648431978499046418570399820557378701901111433670051014534051329085292177237,
  16160850186151552802791807106500962460703640367690328397854874935346467043196341731640695416736511813320142,
  304954132171933666611419788791637284664275373752574273483238634174296046637167293674208694313542475898441207,
  14552518049811626093297424075950137767302456906967140004335732358677864986183910276498576087175359825744,
  1799461494883496723974430780033249512215099109153760058829625204159810398078075641709759781641052708691561,
  295645115141398306250641133019298709688704924169559763617663836636160079923395646940506453323873057136050004,
  6066434307951992688810258833604281967651103020533855315453191922807459242605744862530975081143042389007,
  1114660706628169564503230771705443244545284524870642328868147270353768148431917775353678829373501842742442,
  7163697140198347968716776937526167001565373778447681129338315666221403227332329596500033338895879911577,
  31630598605116228751531371726879658775134509829925430722580569021168098056829664843038978076611248964,
  14836233249613057450477643594808715393505212383424077470624682666517846292436886821890513753174645631,
  188033291992076640190836091605720567312593772942976149109655625723446643703943045352162801089509471064,
  80915967584803830790608201817818582450627690121095994303267632665209666072785544406938019490239833410953,
  40102114615510058123288116892922588373773874545034027190239554748447661288573550310545227693581206448,
  289924180178625247203965113032104838753299829327779472956712702532169581614865416395635388676168681506751,
  7828276836312638105161534948290649450540111459280221189503055578027880864862733117884950687533933578,
  2522778586715199581983119509875913143430752534747145613127853778786480266178075644570436253732646374122533,
  28236598858233611877081602307840143257435740047866742415278416225749006298635215345133165675793100785468,
  15547186996484253495037338120581878317682454077613163488463751523749609961132398033519566041891730435787,
  10461391785516171476333527642016227640233447715360708292543384803436911864734678907963872414159758719196,
  828018484294037666484993009162371540600320005724966604919513472723162814004782767751599764119201235130397,
  9965957223220601570153040514422336195567264452158310859794850869293890480934011813571430942849910916314,
  353337714472205670026754146624933532209430328798955538592477985558857296936544308878824045489907112723439,
  392160738911507275540929022443276815057563399200681807939290818577156510567897310464304935851422205916744,
  1789542977273363856375749513678401131943190882964099008935957915944364154354860872413686184958681625697,
  25820638629950371893182720440434201254308441502261316127693599770957174126503288583472650670472239618,
  3976919069661198376146525714236343115707142160461483678943143123144897671421259528670694950603440491,
  280245487584027563250963937608233894058383282133229107217406816997067157303468295007519568526909548224068,
  132942070126797561330324480021006488593250503468536107214348913375542379198130125866777947626352240741,
  7145692527439856851985462657662866707076585123840065314220325431652361771187545462028915406073854285336,
  19790548713861660126917101405842042631083934971367227382604710699931811495612511425222224614254685932667,
  2327615595627581669405124949304699521736399563886940043305261659087322648746423742654871857278101392628,
  12622150303016150258703839557780009363693756599816019593827551045722731302049052649228262259692059797,
  1415715024212006030028356068565205774485095581805434961715717303762012964477454844163956678725267826,
  55327831601786998303021075923720840999982621108941748335458372855336656096577227786395104204507488297323,
  173101261267097776656782714870957366783114705917872552229934977238261974215226871874996240192869132614,
  11624149641384491952573013437760056535725186330175840709878895024656713933865639838020306427724438669,
  52386694214468235220383394306400230971108016679033820678032903420289380367245553286925488027636845008,
  31724352865131912306812476571422618875641353846675976032381731814592277885586867662249412498093961059523,
  3122603823966527134485530255857214256040789813245892761285494521131929127023181900561842215088377063264,
  40219923763572496763663985200656268766119860070322344256292276601994705203025430514817492586081901053,
  566494703403999053174645198620959033946278746607474392987456989987670059810533818804684944367268614,
  171586546679752447721250675812476841159919381610672224103696377501227828023034911428529361838153011,
  2312922950120297138474101937942376942439124606673881697422522144216105742252030421913496041176014666708,
  556878968766425192264694610494414702613434304757079305798983523063008624144738676796453109796024461,
  1013440570909703268542536128977100718016980151405206896509532351889218713280859136662461483069659712,
  174709007910486094722741122090082678890130935485386280821133356905191416879527416179111729503271371,
  5900640365450856417562368317990043377011931874026713214561565255810559552973022421991927847307227966,
  74645146784463269545434182355000314579915205428551880105585991057887595179010897177161728829075189989,
  40197425334706261809870038257039699749037893072291498944658677510450642752653932400269691388042092678,
  34184022912649320171673961734693681804520913583696267884742068685548394792787937212466512902173563,
  156076286518397277466980319057294638158931415175260374482492721618964076344905684965680538718618730626,
  4235953956698971947851371660510879605439280635979694556857894501300660692428719869143181268703933,
  83128348375433640627830181233164432494407688690170420801740187434608576921643538870297130855220623584,
  50104110731637983374694458693884641443149556975282022565686180142025884666281854226781776892684152867,
  2698620375743490600298690242600491511455420047005433950602237955582886927859322998021609059209972,
  90249697633145369758110065547451426355521630911613534384046133324419295083564334098786057009509,
  687094587768024736989212546724048576879241480867338261449562379955558685311118852259236633542915344,
  58031798866427129101310131970899189914771180830173997866960141572556038882180761473917207383185019,
  14732027020893762066384982749001224867709477365744528654039171357255955534345374474879383528832,
  16356931940727925130949774129930299931269853237373537191196158274285640962934088977747289168287581,
  1784531071425488432749110387198138772635826865508450646358386019717882423287404792847710563130829406,
  142948764068386103704969295956244858724755284955075143544405085720185611472893107553484446515948351,
  264770512751553398550867951443595074816930116378606836388109158256926403550265658211540918240811054,
  7703654809470132478867592873630565938745274580493102053276434700251606314554524478375819999961,
  45578083567809736762654883431616444461005216367958402714027444284350612458549185400066728464836,
  44811502449852497631166984910143494885150352792453143177676667206698615558109117150940856581135719,
  2952438172611717645940459845705461734895454879507800892414881186775362831425641140968016597574,
  281372192042494473972013492880224842722057748055865443499811836636089473454071946326343081193,
  5835563642279286936689805216327558378473635294760907549479156735700621354709735185897504989986674,
  37228462439553357640517120501373469763475839787875116047685354560234003146378197973168019883,
  3829559799155856032735961428550060295322680698686026929238639967183620071629353467127637931716,
  1269719321946192561488261237097158064780487161357363841692346345230378905977894423804929859026749,
  288297741169912035196754635307880864309491893521187574955551824552246033319315758170350240012842,
  739004546275410314817084405421799279184870224719947691492772889374310757547715688251180518611,
  1429397090616488461190583497991732550036132765499436584118377743910393050700299060175990501742,
  856938756965338354597987368417674387468715836109329756189584461095182486171805345052450979006361,
  1885433927898219107758067305418754081598460050413588401092969244447883582477334406495779519328,
  110383684267307559794514571373241328929357682367612898437606372780028192085976982996023112415759,
  75175137111536528403942266055303333659190570668878440211388254686759083818051484724240046673046,
  24251094626645706395060718196156604101184468020931765341574603897023406001211707681306012062057,
  982525823513264451191918638341483987560791349538823093813264102184362931562241332597347028744,
  434117276351391235388518329947635339571099779544533369686904941926661878044431036748059087727,
  1338273816898962472850798302145008284966817525831901160904078202926544550318941813933710546876,
  28046015764833415749723081625325882298888737135423116754219300768257657475445533354225775774713,
  228605617330645986516992714743200530144738206035711902914637729528700301677624167938022402931528,
  416421125885244961138415475413558635105521604368974271326534231727359579944273286513303471158471,
  903870417162812272988538619639216402575538666184665371397808756324244796667597408285077873598,
  315913019719521049491774810475166406345080063006141546765371711865697803965316306254706810302241,
  280346504010160088392651999275421298226933602122648615891362513859839814416057517210522032622654,
  85545524635316175909205944557009431559129382018366053681307758372336742296495728887655911,
  54847471399956854470082528215514146872501409083225469026176740426737608769264542184064142564,
  2374895560693589693886700134291076767956481783207473688072637632898892277304926147617294361,
  344217283528539639824835483386057680231744012621814710980862355533215881095130055282358003936,
  742172837526169434058295388173887158939423164250951925767366188447401091122851482006579887,
  319322257771445445141478344461325417293515775777903786021120831836422932379871220700658023396,
  16718523699045485450683425652044269478046519965819856652665301858982359194231539661556602163393,
  63018982266002760658176908414032459705521629202989321017658218032257853709061497696395213918,
  2019550558654479374130198896846196871708422508245921520210441893829159997882505507213288343,
  2705306351793113214638635526593483116142205468461986836550215681095931951973058025926133214,
  42081459512072209394575328466290657588390521415278856002069864143336808445590263336385757,
  182536090775047693707646233785541638701472619521090555851387474265026323903335971682617142052,
  12124525697303838521798586815028486544929539587272231176434134842250224263559188470413139643,
  195504347705261603700888543225332032941940583726947557109735262158989157064517710476412745416,
  11344974925647143294801583945642562375508188141012097997803687780868519827212129355500943021,
  130448937881291799624622323456470775133962020895792956894665044763115818823814688904062962,
  13556367892181243525122996333861603096379064004733473475586972509691464246083267499731051,
  7847250004827610560098450392954512963481624329789952048905249764630345873973942885904732,
  13671609442382822207430284104883839474495067134466041793933012696486105855636296484995337637,
  3790170834289223293219212654421866712907359133148583413453229913618659965188968811017814,
  19457695975613894694897689544661718520371638695419225780904998261156362933539547830654069971,
  53766440160588283573810389799197399777698682716351130389050690490295063621177410646893722,
  141689467180160608773063689427855520584360488245484237485168117109032208070405254709215473,
  2805831786970308220454301140035630057102084171132412280275868431870495025847260728612418,
  6289490871822417102812239680505640177483291699763399951773717965133112905472091432531702427,
  3384037191381884981492834977381210003386708330351173417746562559664299227374109713402765018,
  25649551614903866539825691475122581488145277364721394245398595897758379873226055878908761,
  210436236744957230948252701243452593657420267883348606892490739551515589298148649022352448,
  2082711197386553300271134825024520413879748062129355138803160862614507442357080307913800023,
  4161622934692673679836672794272206258247967652928044286758775062098441079164704010437748,
  103470829366647155994241997493200738307307544110281439528893443467860052373506236518036145369,
  29108155748389761199329598434211042245922893364372578821002027218605406891978259391384042,
  58776984839258958781575424808492286236326776387131444401792020673689062574828740941959,
  16796460069391676147944932523312229581889163324024285481733039084953854340593185344790015926,
  138315759226580171555538977551917532991923408132933091401823788719612423232072022130341101,
  1594264926897115446483899599854248243758123835562398992192274513088368807705589917695272,
  438728797245799474111880810231993797979277519460379145711201571939250468063792005349459,
  618144400476147872390478685526286789600907513086258088660085818454765278878878165431308,
  29396938084652937461316289016880811525227767035461121646744998996511619849519274331960581,
  2825605441809406634332884320296827268963451846448911056441139169789976116686941595778,
  54853273824875462188022618735388175883000358081410656576144293738255928574959293478799,
  576064981249136146237894493052097640650205967207052064092843380705445919038239802129075818,
  402936606910232679813132543442125686616544829251393765690283806073261303324990485579837,
  25906827253912545741202696961016020421698662893859455091492155522910406398033048049286,
  15727283831920458598461673003129168378931866695134335219848173996197198834762240939211,
  3426797742624633774663917382126227704672977223803952095148317986333939190326814759191316,
  501296323965474942264995975298868472125586719245483710361667486662271932098416827733,
  10429807464008700812466849158760028432386567938856876293449740989805427199236494086944,
  2952125720644315404720688271669705951256100933142165816152827594276930628977490599882443,
  793075587266023237144442598971101163579162945405898402171346101141055061806980564366018,
  6278395023623075754221478981677054180756940171332004394821309365012629317185016222349,
  18439894774818650983311420184174118371386567304606371251339966055443792336868876105978,
  1718738629073104648260317703852189592080476160846594181510288943284173767622289267331,
  4730155081525758476908575918037398890474873666242154026927709496710102159919189780054,
  89244008168697703239454295904695742581756332758586189319709746877400929209364701857,
  283544531573917758496871406240796508387684263684693307046996686891885519169225406902956,
  30828348234096431910297760851250206547980298098224419610539107741078707785149458321823,
  1404988130211731257588894688908081485439111941898885667417358757163479826882256672124,
  5410287618663618154127404850379929186597053521219622299847992061345483455819319880578257,
  1871787659066939185193343569605705323715913055834182685859477975163144353416716377316,
  190734133017572089493235313966490602051573683632239753439012474164994314050333155431,
  790354930586583398734482848598165338162619942088829983064302368804357644218038873985152,
  4696377724329438396539548217981190724952355305871149604505026344602358869381761041,
  32952389645522772320811364027432740764304526527606846269409302486958906507224345874,
  1784713816752137124259073173965741220099909471871938301319175795380987755842462842355579,
  522566990405013596011198020241540325899789275095358731463915109354903968427848927694,
  9951668634022009795229440283750892697024728262132622207736504902228128772198950442237,
  2170957911953769803021389314632953267706078010054132257029283602640267030979074344663892,
  5893220757153292423890332433915914945108835031537198135378300161462635384786227191363,
  1536566044401312423228869140027916339147320752011604057341921334819603300109649802544,
  185910648562970073369288661320083091566844284155099617075899881432946301834472471677,
  60306435593123055500747216119226400480608996972375361627302153005511296762423942022,
  3981887409422494751024731452686459951632283175770823647327551194291854055197695116959,
  17961348807236157668984942332146724814271052014039604940539964681376590677521349756,
  20458262808502566393665743458528288477845202771149275803970289621329799917445396649,
  19602250258294291976299946119957487486337644661416746849926123183620482012690399756268,
  12547430440449674454475187928645519390850668263184036603552994636686270756829943511,
  3901350426300922100131667944725999943618420206469357293854101894302458365871130244,
  2132904056801232905911130134530914930754226795835640813974177211716923693015756956657,
  118539433578593004127481426151578765991349008729898676665205555220778515446769971882,
  986389768894008546178481412555645124232612496244777515331666188242698107897354487787,
  51580840911235655793426203255603605480060544027196755180829197585314506890790816,
  2355207049500501565184111569896050365560125707896012806676116106596475435003500605477,
  9891512971653686924040008414676420463281781693324573317327896706357767874359324,
  490397395913676500618001768054656714921803436149160105929643556310458481776343659,
  6208806191620589319501361931177898465707049164337617202968495355543286970208941272,
  2183984932394984335846732663791017383906552841538417518606546635343826588254029479117,
  14135647461268488737789828573947743383012921306393266116694744738574889401060990972,
  251838033395817390666480853497609798396927714389384658221502279938161340701897011,
  362739380765987778247349068605844532552398005142789663739473850789757891395643882556,
  1827089539095030927234072292833214593142071378368259690587447976329567623277628019773,
  735956356427858664307337213910044139734692235311045258493424730249237239259597955588,
  1989721389437413947862320599122718665044952481390924783463156778782622797839846304427,
  553115459416731740219629344390325959983996686115916147387696853703638435908792289584,
  93940824984365828282815299736372513063424226100672805973925713920998490293834301,
  102434986473450730987164540428340562213363191593558885648381550470214600118541258394,
  308845667285570391610882678314660154548569119095625404944537187451307954475465703,
  68224685102943831709081435080762338904899163010708333283835801171220866482006306,
  63166980771493478714128618639251239296592883206154352893509328646819881119893049,
  60052995710397856836216489040892953026077304689926575547522164942914283988474255768,
  420589124453863408860776925446466446065214924157698562076975765453564564273231,
  145220345257647823062089670473088155156963290381077343159267685945457299219988521382,
  365253783078358066615485922816242621485205117171005829171436308897465229464833,
  7131490415491114915250793393630802376577811136330774646925852170015743081036182,
  2534665616071486336551127831308689336243810522015336103366356473119036177815051079,
  13067891161960822396128354348515148981324162271275773502522166025577149865452,
  898523655315655007479683560745924962859671975636867621333145932569109075331256809,
  1727097767069891155357366253017076321296871071519129191511510695818471259703398862,
  195572394540823368319300699459024213928417334767578251586984122466917799751915287,
  47329692369327318496996557147695344907545530395337996198184866403207429973068152,
  13434686804930080968451217597351085831902903973090306763020257246507023751830457,
  414405518719009419332073542852111169398096709495999577429463488007916812032432,
  150566311609019361015428215102956466750139868462649165907102703784183542672061399,
  24115356113665394708772421420916937151346589400944088561244692887127237807705238,
  13694853484123133644136590455115301549969650995939155315834879131218000964220933,
  191315114420489310117112305443096749921584750106998431557042560975828914976,
  2567673684141080873902300265358990335106355070188735966520068539008726610979,
  84495040592402259772174173671649672113700010139939878259247061814027960922,
  61643897853220946333519688029986156852774897288034074154683285728940535342870693,
  82471013971088391019620300891045835657241778064472395879599118577980079932,
  30410242655879768274582192550537785934552914472361078224236755997258845226619,
  20313944565583228257700377278055189239328511412172129774462574340058886915104,
  622541177520530898453968164445188672372368557664975331381827549462443252661149,
  18919665517565089260760237719620144403565823203360422565403190199003113858,
  35003326544747488876823631206912323312826646804655038023375810005409360084563,
  6984970821228620316406453158298196254488325535373977403726698324806734341758,
  16815220551443526679683245421195554822497026938484168918598102762623758300709,
  562732939205189742992024511268954385014844469896191823629591368002140405890014,
  598635620086675242522317521837754682791072483995937061532520764664291159856651,
  537842692551104335050468748092443017690323858237885393934304417571262792114804,
  136409409827764663877734349747097006229787434151526563098884425760229868013,
  541441014467259730314096648795232021215398221100833342382159622747370197248,
  1990258877095965219691180878445215015163438193893356232275077009463508651,
  24373359956385483779535830803289307630837670281409233017816569226542201926,
  24436215255953756347138681018648639401940259849226990488160209080302202277,
  6594977661855085960566528475138440616723504967938890646838709725986586478,
  48705902034206655813522613819769056591530875530870682951565358210617734023,
  64520110729433748611572570320436004250582334600869526921074181551294797926722,
  3484074862957361988424853654866719945016015147851271012532912096381042342873,
  992054999286286946651888918537011223234228137831208711200468851874918933696,
  2538251831489533724549141296270631874195018578800057696445812005401205471,
  1834207554171271538694904826861860518284807423531170486253453619473713622246,
  13188079993721508113460102504377804807274262056759529163650546912441189737,
  976703127468772546284038583388127119208281236823086108177600408394442116,
  28331655666085909370077229400551819828323731697625624353972608614531907951,
  11094238713893806290433290505408907656436919600820085937846888044492074895012,
  24035686986877957252483789156495329579266176602886496462315775873693291009,
  19238390249019926989823479736562745544136744186322281346301073347513359066624,
  3607477483585097611675236115395495973525650558835507599314603427358893807,
  42436293552332282666200577054298117662584620235998179697388814025133073864,
  14438432999841379681744171899302060644053910813623946406647995636144016521,
  75325322725202490956121028512292062910797627298513416305968753885983978238,
  27257488463287075223290776171272695683444025692220874234947902795873987,
  460644792526037439173882240737092234465785585441196768642074563366742198,
  410282365139066838834661084991240736731777570871739861299241727550850689,
  34993973756073778587273520387850556335389128906174036787971442185526354612,
  1425953383033421060109790045911298038351077959366395438899625611556403806799,
  8638273161684707858503242169854021759171021091740066102683504671882434133532,
  530281490955736155875430090060983406218686698531283245928837720482371001113,
  4725942654744203519566130271888970219846866826972689456055364522689360624,
  659102283569513622074961457288461522896689610430480355232291180236228678671,
  54693604798077375229854301891483081816301797065821725413991053663805328,
  125480596624878795571364398926101111206060678487167785020445195438801,
  3783141882118523849955213351387364570216883656799476645976172992741418712,
  18301301245431032872995590765856366135603512134092480950920788959746132887,
  415766406378403917324001256974618418037909964950343665610408429360982408,
  868026624330255731952889448223699916300645834796401064997732145023976953,
  8063639346692102912755889399262089462083070577374156203432086057814,
  4019921925034190369550755828850921389010005781571974493320450970139237571,
  1690906937417704748698911135579410357775705520074780630263859153743973476,
  34727612927891461645469614641878423835877074964094834397371230175781,
  1212349640301952763721323658852243777129971650837665651929134185224864068,
  1277856988868494700935223985916262688402349714066099993262645174571,
  24716832525418953480300251956957574468151680211961391554020414850962878,
  1664306899479305746918352996664117435591621080758747640634770216118593,
  227004211297683636393134905072272044345968885263683668215064050271302,
  261781072458227126753107738611151889820396528179614427331053080652383,
  285238092617950350783401976601352404051148898101105485410875788059515088,
  5098160300411623634481760721670453810832564676293673216374539338681,
  22325414797003565739432485457388951372274908892039312555998279281592,
  87303814043382118146404699912951280770782690071832710812239975741423,
  562486956949451329283891237522361471591759814186107746915722087404,
  75033505908201077354236799686413122176820395248009770922467839907977649,
  191724511414931604397191713272956533261822361655121809222574875256606,
  827453256049905088488377463146174160235199602116974060086421780030947,
  5528553098051280188525782578806184128899499760873319793715578645442,
  885467492951355832821154366483464378962649090477931430680680629,
  20593840831682794766672919558943489901948343385005115273421633026,
  4014783129093991927583979502801847642170774352521791937516561723447,
  6061802604309907254013908709898590264961034198590906032377685872,
  167899789696750888077940770172477550816069865373988457913980871136153,
  2402970326468401720185700420337502330587898819201065987265650260932,
  86166286743455722648172211544649930884406914156390240607634668920999,
  14097081502174095351401785317133523911286478123819316460484775185054,
  414409494902805319708124079472777461354311752204646096030370089,
  3373451451811410512864396596887449779479385783707463443388743456,
  43878618195772207455413729390037215557954380611643635434288304638711,
  335120410576817320656935538780674345629577968622028338730347275622,
  1570352392139577601782705892104653742711683976090341322848280137201,
  178421792725910431600416685918089057716075373891859838785726638,
  4258459481018157453424594884319632650900717347619354312283436651,
  436989951757901090853981616432651356863554245380086703133538924,
  42572193135120401437340985148693406643747715274458659605889981693,
  79774050673352404655985622812920760562920283082866147102117388,
  350910133485290589874569455439506544486143786636397878376344331,
  9755965987505572431963632302958166498818439323697692429176574505634,
  235220989616169896616416673205988691231081325204911386466090523581,
  1176196825889305511687835817718614539744306617314372520127774086,
  4923028232377161238495542175200031767230031338430841459249195107,
  108676459490585011112584663395601830292744482976444022777147566,
  7784167985524730209615502329755149809684786019091751198238529,
  3346172358525510856522881950416383025164627716815112892126918098,
  2262887496083196967119134659506003711723783779001426723117993568191,
  175377713980610852442949184722434905015192628634525150782758314,
  74236339296082718873785370120891311333018928856868406411168625121,
  25801232196860991296485570327130367166836427220933956668521918,
  19481334523885294652693170118345055457996794785462556391047515243,
  2480966647413207078011271514782069784686657669236593494728706,
  485276306469200035985396276672479586428053219423509228221417,
  161468128784967445271079451740845048408294272526838220287504004,
  62667587831950862928730160478250903420391459983168662870295151,
  2556923638451906520971109548909728360791220727988323533228311636,
  18824341575458021800730075823189757598390020029814383464279490793,
  9859675285836706326225970379330069468510632851177122134459996576,
  17734290353197345949262497932318396774469515070653991002599,
  16710871739072660372913203358865413554326699117768026677342,
  508303911031352914074054133828880741109741877677825266459010657,
  1776235697018199039887330403275238485187906910845227597913795262,
  3327689485538914919320670386948456537349344373920191614390987,
  3949650928040210680708893630519742119638439819136606331689752,
  181389501809683698351865314516549419793235812816095408124172837,
  64892194654390665962036031257718492616156744671661369463562852,
  118074916144041839183108815623111352015602873251393922619807739,
  116458889689091280109583240416932323191696397689748786264016,
  1191607197836922285693452782181162119549696680037277427293344501,
  68025906480315189983544028869712643707217582187814945998902,
  2217123645955842522250372525373835942672799263213256086337947,
  296300472423588374996901873016582865671609789411521414923758,
  52713897098198418388569772433201339841321271977804985652177,
  31248192404270513179710441381146251671949863728979949017151146,
  931464509894839846437425820487836319808776169070431756020183,
  201388077907758234196981846505943870243302800124683941337038,
  3067655454388884903249274711845424132827654442485174318167884589,
  33227340561079279709095889795466881846922902170622886572959678,
  337625782093410238791856209848497028945898959286171124627351,
  2112049248457317952154566427259266795172796899887127724019220944,
  5409445217223345283007548234987539202239941654765727550582097,
  1300115470236614948528172990426754410684038867933053141065249948,
  354625148530555037363280004412880230519336796220586271286266871,
  12530255483863442208606568697400006364095625676535401650796,
  278338992861669987484804293870237685687405303994210701423633673,
  188775954153097543419598717846133592611685617429158274608812,
  97861635925786435191056497255406235496359993520014471002624407,
  106031455871838954841045511875716068037160176998262476354948,
  249540274316875906949873869323381283011642474279671508809,
  23911274553878926852127797146100681880985848330921450487768,
  3547481350094912452815436116859980420341378643980248960792111,
  19099370820541770571929535421191803118093701735968881291086,
  1736150133223410333356313707675069408489787235430737197341,
  61806869835618221216944818448844755041975303208128844831836,
  149754903490687331478965045271753851783851792994307685891,
  5964424809286953836927188329984410442156711395606176773517998,
  1152675576462944275874497331341998412854647977506911420391941,
  1594325795843719082229852206092546211462858641133837678360746,
  8452958561948684852101867831706181257789984780068729567,
  8061723646430440300550648357936220444665861618040819177084,
  371559413536482490240957482414988788896268737642577636641,
  833508793952322877659817181996729963281482681198580472592,
  887991392569132814416448212869892515480159588895567269751,
  80765952041576208106120331943345194408836474150853035324666,
  1267396973935768541921157617589329857033048007017949090553,
  16986216957376258336065403920919155603136155677005879214,
  124414104752184449660787393544108239788212366894620200367,
  857028815135044176762322470291690007200447375846816720206218,
  4804885561871064858081553878194943915118054442935088609829,
  537660758511597223434434210868593016982285344336205129664,
  310967471804776351423316887391021139597284567117085632001147,
  181729327321215527851390639328604256845060501487936632616,
  509451383203602131089424617002319032672804875757154069,
  64097184464345206264984729408470821645694613209527311098,
  1772166830691325949840866107422449898053238330042194931,
  356518791556905468547056930286988323907205873182594422236,
  29970312973687457535114299997094560870589211198142592837,
  1187248613318775531855271302625915613755639331582415038,
  8086394942950433509545897071198830970582171932239912063,
  2987091934303340533400230387812665585017794226473227806,
  2062596278690756714442773078144828607191727982553381,
  76525954151838171895363735371564315209260529086997704034,
  983572706461401100009693508786162280886526292856879,
  2349190368233516391463262652030113188884607951797222,
  207817250672769173768070865321463492618926633885889,
  2059630779082905808124529037641510590816997489773924,
  233641760704175390227045410741721528374098836876660663,
  13922307329297295890052332146563900746557586659520897502,
  68070468606522571057763917967546894016407032422280352609,
  343877442527405756701174061926934258325443952718478084,
  1309438561244431758761191576799261063540815227657559,
  1380104302828516930572031662881750614937853204896866,
  185645256331037751838906924129848297019249727120365697,
  938950023051363856471449637232922343644086253108014018,
  1210246953804687860756806471477695873314640135184327,
  30835832343908753890109860866540980050998782214662335024,
  37573521803765232554554557900662735656054579304073,
  23344530929206536360491998802168431121707391184806,
  810432576665766296001579314785328149185792163571775779,
  1658305680561064485216590616191507223784618027007752,
  31281346462313424653517086031369434572779873554920557,
  59178764206727640837816804784369521181928446286174,
  1711477041061372030118489178294855594582566076128011,
  108249972057413281571371444613450723395997639882630392,
  66171723167493011161428085872305457933258194419320269,
  177701594012316499927085514875933065178075133665332026,
  1335937360098497375840260743486727633767680458846790587,
  3706160864688474878434773150162292892347076357142158746,
  1133541863352860752349576161953815785088585211348304989,
  73381477163860430560052897938060084896571319313837206,
  4235792108236742245363120003538827202338898111499,
  4109721993544734576316866422223751191623126379144508,
  110140941882199993108300637086268802291641846558197,
  27089663212090356674368262600371635852482781123728,
  43024247483017452944169022771887351028050924404891,
  738024227120741359937617266693526271114514487792199778,
  356653125189783441716200794819415555655821086334813,
  220334065419051596447142201598990675806909559465449426,
  1415738141892301863401103098301003363492616000865699,
  258198763140690669989487618577551715735966175038,
  979765137545666280789946047639569817934455355555989,
  106012528524934866230737262151973136650424596304,
  12872356529614349634002284534382714393963067052405059,
  29144853028153996152607135087907802201218472306412,
  1548104175597236491222377713175207774800639448027349,
  3623083089029395516722898775306465607533790770286648,
  352075646659775244514194618793095459061347218747,
  30156972164120288054250911297210965656685606529696,
  76307144965629135132045678744316777243474773261,
  739601578310714148899766704035137911495583591682,
  761274960854133291876434039118935014665051740480239,
  69637178217941598081559120991698482935603732286,
  15933607326937094843980917110508846538721842894375013,
  869055055747899654217642019790529340401370025292164,
  6094121207420521611413783376766185982768743909667,
  191200605317538088147846129352132812894549550504,
  198484323801806144499182977638980232967792173837,
  6947436696351865793835151974369053427763890039214,
  1334542904917991925803450026178537035961680702498979,
  5112170679714796053849604545032653100226165176684,
  579284657318361132527303435994765891592920039141,
  38579662043322478620267882430151418907342792852,
  324611339677789734594657468902663312733486209683,
  83317114250296997970823779386168305776803427573818,
  1561264314766310157593097571158240359279623955313,
  222587476824221530892483541916456320438806613409486,
  99216566582881291327143429821544555001253282583,
  749723346783408912985706846610544067282133578,
  419231024704357806520705234148943659534212276956593,
  5927198983329416133332910810070023448562206299514,
  260710065568476298949875756889951361899097585623271,
  218969188313018962577099427223824344577484321180982,
  2296553289148162186068309740635037853241442989,
  111540768236333378652073652906207512412495578,
  4300050992143697919322630615511632297243761531,
  17878859276099530109074359996829675377392764400708,
  2100682342406395041358525059960844616301133813,
  3471804800713333858343346103063323828167230018524,
  16136303106602056276896326578294179629322994551443,
  228711791414961651430931936686845547700102321724,
  33458757324488131181949028321688496820213669,
  16752050514377252655477998972126546676960782802326,
  1844575142515490470596596284744147806787268039,
  6471374841136285792645510194447449807493172,
  1184054267162027481724944302562297229868193,
  62427563008962773200459983989900599935013088,
  42449231442896572967495630342805404517833207,
  6466800573982365257840912989574299323471371062,
  2899963661979981049878864807699040842115789981,
  5831979483942188391150244661251756542844718,
  81338023319172255113015293104459614987411403,
  867052646479416766796380841235355012225474,
  991638395474111595591607591663599392749261,
  2516630347541913601923078841820841634387223358,
  130452640580749393314860501607598960611843779,
  100170444539042216052668301135048929923594,
  1289576859217590787505679068296376865335941,
  29384448017503836318050451564226592948957238,
  10558067014319818749263763860521092607931,
  1675399940865770242196038019592447045716202076,
  41829170539197488614991936374406342788687893,
  2187486406190761404410282388797149427852,
  52689715577295758660475747196027760773075491,
  12447204544942379226767249253615902087581522,
  2905435691243820020361991750769891297232253,
  40854504871367201624343144141379825384122186,
  1343909922087796433914102613474115972023639,
  537966369926693343053782022179937495706474,
  623847327602575427082681394627599940249,
  82462147743887278759598057076015851638869484,
  36178070575306274923465283854397645120753183,
  61209402997530101663027497960606665574141998,
  27375183890772563430628424356212902249701,
  170221906307327118562041725588260995088182,
  5658498739137978773890406315287188973152371,
  44359891757459684314499627248181321826,
  348821928968210829513432700821828036539209,
  10447424179576798217936344286530055565908,
  615539830864145171521833193814737247887431,
  211496132134814828037592007570203290118,
  20666293347694621150941815580723335958753,
  30988811482537748705229842347131698257124,
  143367810287981115659757393596753210103,
  3539136783107491215261668232287995198,
  30174421401367889968837474704941581449,
  10908012337922400460987237189532912345528,
  796558826084157464779436466800283103,
  30855817280010648052971771125881892173396,
  12220776628640528056737909625773062849,
  456438859589274379801393436435081191694304,
  108021345375004050611421382405638606103,
  18032758348201838991143378570448058782518,
  118030277803929830610058171562706537509,
  501687106338158613916807042824485740614,
  354762638285220150521274016723003670598739,
  478561588524416701245951102302919966,
  18137094882245246811802928585853159052193,
  141003185232782753382886431973346791413834,
  36317748460045980281357474184325082452447,
  1673525193627301070000594577978791778,
  169020582040560552285104779954257115457,
  4166648901580757933570467759815946038,
  491605543087893711513022397881013179,
  7212311773336423131439686264303226212618,
  2911499542571042504419198653876603341,
  388542379080199130356759309654489403574,
  21793639750397767110178479614991912610831,
  666991543742070225883429750546331694668,
  2827939841723952616533840813729879092657,
  16486488561419159441632036923590706706,
  14881258245763656006325109559370386579,
  68119446210966329762898719196499755044,
  214503025105488374427265038650532517,
  41752832056289710638848602821897815304114,
  1281321509587440155584827172845210947,
  36931914044167268469911063728040184,
  2537834022332745853785030643560315493,
  196880335069741705091375571826096854,
  549859614763512762099092257696946423,
  361394367986120057243620185418579594,
  913393145932054737583166412750737389,
  1650357225255978210508364820469501784,
  196194243611564073649460126194180227,
  224502075942567773607783176373310756,
  591189725741984347610250676451350981,
  1013726866277269702366961157316254852492,
  1103399335635029022728792406819767891,
  1205414695161755955977700211520808,
  1956263757670275454567546631257741,
  527651893393772524155986088164200364,
  2975353701102886507283830727406477923,
  60317816634017333515871744205056452,
  3297410482152572948666101373348120389,
  244934515098712104359623778474730074,
  48009369238457057393723141713240743,
  12209089796864049932986852420739572,
  24596361282671864310462970737156193201,
  1154417602828199707776572953344803934,
  118113956143990599218946895687113966143,
  1998440987792128460132953960909314,
  1439864111029748633345330371958342521,
  1796597694138540644288775915234037962,
  1138904627102869506533068879106917379,
  71389376714839991964408931316197474,
  1153527488440373591457350290087177,
  4801016571498208366617089458450960496,
  1606728537686861743850993806938863,
  2759960919359465050597227068587337122,
  1025107833049831072304674111647201637,
  1028810097874137662504290979970586692,
  15265619275228785554142791339243,
  547185227028673930613243495456365514,
  8676028773005429914428422373813,
  300127940303517040067003736380391394,
  3389762483312755692726197740167887,
  35068839042524749350428961258366,
  346025128213394360011864998214818517,
  104135394143105981785249648824792,
  33599702108774215139237100298809947,
  13684677689649628878366348567024,
  268206588684280046653558184156173741,
  184828601149165053626873132234384,
  58101343892738591518780035411,
  65681953276387045894352236461496,
  3020059653742179368986513236914861,
  412051193291368356351054385729746,
  7967774610114527803410690571,
  71317584735441245931932166442,
  15818124232855553843024613015909,
  490793512979111861867362356956,
  3279039718851865055590700946335667,
  274510467108966271698150680206,
  88358453191612048301037009029,
  471380321184078134845913939924,
  275292322253901703513194750668379,
  890432793812139590490989149108,
  59648426701202688651795980173,
  339535059288194380230661972934,
  397693948696881438050183343,
  102479305246988315680194194224,
  17779530352223755670557826016081,
  1015371438795097117756266770462,
  133706760081578095642782049347,
  136430281011634601372446110609832,
  54399670929803355718359727109,
  22542201176952130751306924,
  78281899095366853888034998531,
  787659355615839362744063842,
  11660761559527271532579125289,
  20836871088951952622839574,
  364835722695333513774012243,
  567071623062722498732756482,
  2669197143654907394630007389853,
  187539296610423886171727726,
  3844053976100351716796749366167,
  8816391527976732837869062,
  2687684578151078461275226681381,
  4367631420372442063989582,
  19379114243143731334123689563,
  83411902221524113236734004982,
  1214806212942051551975031576873,
  550758700644644138783858,
  100218746684711519238464643,
  6282958462619759831956036,
  456349456242371383756781,
  2325860311665934552124948,
  13172478021227584165017521043,
  132323814782842646178946254724,
  291036919383484530569850093,
  8578759356888132782334158,
  1510010808719810214444043,
  27039835128991885954297098,
  9823094311134155005971761,
  125773737922467824713253008878,
  2918050464975932228733564487,
  42031484014584635854489358,
  10836422496289278310994539053,
  14743076654443229927686715992,
  3219984455107011501950590051,
  7185693566246244197015258,
  383389987378179845639493,
  710992765173936794382742,
  1331665374445549495897911,
  139193273497523762083866584,
  279163190639604366078287401,
  34135559424983575152474,
  3896204622048457458199523,
  1236779573991023942130192,
  572909119405974825523789,
  118190614462371017235031306,
  4810219594965298173802617939,
  1632962961436841294319054794,
  19623215994195262395869193,
  112240306370507939382724,
  6793475391829683692305952863,
  10129820594208118659345062,
  42325493750742694580638353,
  1439024530475850334500346,
  286879308736300643290687,
  18212385538848873777561584,
  2433826112786940761601,
  72161809149036798056692,
  1203044390191599389101758591,
  2033670698135859033272,
  32957628356196354360028881,
  65002103239204107953888992,
  648382345022258836270439,
  318925533627392724957552,
  538477834476093188412169,
  255291676668111294656,
  3733623603237542498807,
  898592883963148458334,
  6355693752877024581009,
  987451359726835325702,
  729077774330247704114691,
  1471908211289144707786,
  23859947546512843676271261,
  1974295726379316173828972,
  314252895882612227011563,
  26364276720588874698766,
  413820028980527844313,
  571432091669357806249682,
  20964291993487216261607,
  5426261800050507557623354,
  27768687384447426495321189,
  11711625426955761513809618,
  1753369929616500181167,
  4059205041410449216705906,
  9330769977765354564504249,
  5115901743127271489888114,
  4433515366188709027655551,
  2350602497238040605384004,
  299258812207088142919241,
  9519153681412190484,
  33265771859070700063,
  350629773782860994,
  14278146508633039976553,
  813708171868511432878,
  21817358433418909128139,
  4551455047923260739332,
  1780306914895025692661,
  3552090250291087983538,
  481660736023068219,
  4957764983572843526,
  730039010146918858137,
  29396353373081142112,
  957120099053370743,
  304842675894654395336,
  36307104697273581049,
  53162584865746009449922,
  1859263738670477583,
  18302443872062222,
  63939573108828421,
  10119802861760306855346,
  212203887797315411,
  84330859524994438,
  122828888187555909,
  120284564952621885932,
  1986390539093741761179,
  20786564026517704,
  88329553227267549,
  1271211609842143196,
  64042772606483514939,
  54795544042070217526,
  3843609643359719973,
  6497190163452027704,
  122368584821164579,
  8309312491390305484,
  78402450509603157,
  2665282283986352,
  379114765650959931,
  11739856163040374806,
  3929337583003850813,
  29556693626519814,
  40876086568000575691,
  702606304772755480624,
  24233273568234701,
  260458297781760516,
  1797150944112859,
  6553497442591733016,
  225791494263293,
  3116743815080158064,
  176653885683083329867,
  564167042862264,
  6771703592793638093,
  916722358428014,
  2015145946321853187,
  25777046628685294,
  8363236720049883361,
  7274570614572636,
  11137942057902551,
  132586370133656,
  18880423540255393,
  9818302252518187228,
  673609662191639,
  939533766694272326,
  141068429183181,
  8347782301252,
  718108988906019,
  1289915225685104,
  487540040436833541,
  4747342155032188,
  331587581569613571,
  4879858574479742,
  581836293529540029,
  180778027964692,
  259835993185444803,
  2302031603217305294,
  10247900342777,
  13095845598360724,
  642319816231,
  5965823806172216,
  2555459090273,
  5534561643953986,
  398933563603,
  125896057838,
  115919740429617,
  657608563486,
  19914238423,
  3605278751852,
  17361383116769,
  44132984664,
  835348399,
  1137414724846,
  10204053213,
  97310966756,
  278456645707,
  1469475246808,
  8136277051269,
  2105724337484,
  1168300123083,
  259319542,
  9228952797,
  4247257963898,
  8877424226007,
  13548167137138,
  939034573981,
  26569914932354,
  34475223719,
  21191884,
  2127529844113,
  2955942484094,
  34701000023,
  119959157628,
  394030441,
  836920572,
  284981759,
  14196186,
  261768613,
  216101664,
  25636041323,
  163274,
  1234521,
  386572,
  8674191,
  30458456,
  5021609,
  63864761736,
  8941663,
  56594306436,
  2288657,
  532562,
  3032383,
  674712358,
  48773949,
  3302277332,
  2313259867,
  248352802,
  105981,
  2413058,
  172366607,
  14318432866,
  28641,
  592292,
  299043687,
  11025712,
  77513,
  4835966,
  1962451,
  2621548,
  2214830837,
  505639674,
  1830298963,
  11333908,
  52467981,
  8063380766,
  1625843,
  3008844,
  34526917,
  2284752,
  515963,
  228856,
  9470629,
  1187064,
  635935691,
  6137388,
  136717,
  88302,
  752771,
  958494858,
  1462119157,
  1652022,
  60611,
  19204,
  20029,
  783090042,
  198047,
  3563475832,
  397041,
  25736,
  100992927,
  122632,
  1016601,
  16076,
  1991247,
  256,
  4776769,
  588,
  123203351,
  3342986,
  11821,
  4425636,
  141587,
  212492,
  20320197,
  62368,
  374740947,
  18473534,
  27337,
  75995586,
  129198587,
  588243606,
  49,
  162,
  2938607,
  111698,
  21,
  4,
  3,
  2,
  1]

/-- A list of positive, pairwise coprime numbers gives an admissible finset. -/
lemma admissible_toFinset (l : List ℕ) (hpos : ∀ x ∈ l, 0 < x)
    (hpw : l.Pairwise (fun a b => Nat.gcd a b = 1)) : Admissible l.toFinset := by
  refine ⟨fun a ha => hpos a (List.mem_toFinset.mp ha), ?_⟩
  intro a ha b hb hab
  have : Std.Symm (fun a b : ℕ => Nat.gcd a b = 1) := ⟨fun x y h => by simpa [Nat.gcd_comm] using h⟩
  exact hpw.forall (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab

lemma solQ_adm : Admissible solQ.toFinset :=
  admissible_toFinset _ (by decide) (by decide)

lemma solP0_adm : Admissible solP0.toFinset :=
  admissible_toFinset _ (by decide) (by decide +kernel)

lemma sol_cross : ∀ a ∈ solP0.toFinset, ∀ b ∈ solQ.toFinset, Nat.Coprime a b := by
  have h : ∀ a ∈ solP0, ∀ b ∈ solQ, Nat.gcd a b = 1 := by decide +kernel
  intro a ha b hb
  exact h a (List.mem_toFinset.mp ha) b (List.mem_toFinset.mp hb)

lemma sol_dev : Dev solP0.toFinset solQ.toFinset = solD0 := by decide +kernel

/-- **The kernel runs the residue checker on the certificate.** -/
lemma sol_check : stepCheck solQ (M solQ.toFinset * (solD0 :: solRest).prod)
    ((A solQ.toFinset * M solP0.toFinset) % (M solQ.toFinset * (solD0 :: solRest).prod))
    (A solQ.toFinset * M solP0.toFinset) solD0 solRest = true := by
  decide +kernel

/-- **The open coprime, 1-excluded variant of Erdős #307 has a solution** (kernel-checked certificate). -/
theorem coprime_one_notMem_solved : CoprimeOneNotMem :=
  coprime_one_notMem_of_stepCheck (qs := solQ) (fun q hq => List.mem_toFinset.mp hq)
    solQ_adm (by decide) (by decide) solP0_adm sol_cross (by decide +kernel) (by decide +kernel)
    sol_dev (by decide) solRest sol_check

end Erdos307

-- ===== Erdos307/OddZnam.lean =====

/-!
# An odd solution of Znám's problem (kernel-checked)

Znám's problem asks for k ≥ 2 integers xᵢ > 1 with each xᵢ a PROPER divisor of ∏_{j≠i} xⱼ + 1, i.e.
xᵢ ∣ ∏_{j≠i} xⱼ + 1 and xᵢ ≠ ∏_{j≠i} xⱼ + 1. Whether a solution with all xᵢ odd exists was open
(Wikipedia, revision of 29 Aug 2026: "It is unknown whether there are any solutions to Znám's problem using only
odd numbers").

The 24 odd numbers below were found on 2026-11-25 by a residue-steered descent (Fable session) from the seed
{3,5,…,23}, and are written out in full (largest: 62,037 digits). Source:
`odd-znam/odd_znam_solution.txt`
(sha256 b1fc27d290663fbd1d7cfee9ea548ad0e8d635f2bbedc9bbace3ca53187a9262).
-/

namespace ZnamOdd

set_option maxRecDepth 1000000

/-- The 24 odd numbers. -/
def sol : List ℕ := [
  3,
  5,
  7,
  11,
  13,
  17,
  19,
  23,
  971,
  73259,
  2125709,
  5436803169342029,
  32402505049452208724387328409,
  2529850441050719139188260363010673435393359874028402188424763,
  665271802602754856130789953401799467675789191554080574683161565455417906062328466149699230971841324619535959608555322109,
  288640702804335026495211535603446426365958101126534062000266615016236763033139297876565606160005271571210596875805376445689970787733893979839998352091273959424554494826201621648526737828432263564677771184071691457218468771662875771195925714429,
  6531358120231672989794889556787254503602700462286283667567857408591688215977754023022246927967271580580497430289378195784701143943483579874298053345456701910993629654242702970195970012672036005481932852150577231618149603276715639449017268345170533881393045541663837376569043787622775149560075849153000414237447215556419187828108275751443171628183093611977348798423920172136371154111054600180589580408975100671322251560588237617340684090292257606828137931534073818765141411420612900289,
  2301743926631429566066951509153845717575703207190636742991390398420230253513790816709609343965016014692151143813451852543331050774549725621717312008737390893570073136136851950274596175076293631763738748476127311124941833917485077029345697348074002448283037181641371040731751787322888221183835928123789232677922975481006570108728869864294321387150451615757369549337692983432980036268493886979005187830446115578490503564198551339998734421927067596638577813544832563022222491138558403540650606500125530014468187100497571714996438341038194823043532930517602378039179128309200423395716555535795920755979694843659267144538054985435898078991842469191253754191138402772350742357148883188809685255472605943594182009043969017640382709864829099908040705647628996935437431456005079185868099496462276041589302949754360148006676633548020325433934077538214268011831108299003715072817137620055412941806006867832160841157322695913746590245987031993961269600626303429862329933766974249297,
  1876088080323507888544273568488799274646477899194402163884195713663833274370046875465384296354855247657726914241652725625317803339445402891704293364574691813159381017543442375196215370007869956553620965708446410623862879924303293475689175805874465626839054881545534121549794631487804712579570115296086755777808920893097524638560546814713650059086299658808259091602624680680168074634805196102836107454760380502314444786088114144645183590897127002283752460883228633930579910201870506686477307226044160501626947286242232653552149367115075807773570938180876720838434461202036363875476163596197951084265931084362605896924612864547835542264495524727820096085805949181712502124475998642205705329502751773978137679528594743730603963495567439672989144281299861972946024836205511389633667440815199456184462918400751768732431763211743102841081860205697828903029540268371799237729584306845419245032593782465695167507697268059200670211494922553898223535085770613465517783018540582023932959154466641924355114659698852390472806172789519558202684057260078166807467564873434835265742080603999185124471619052057747856014255905259252897881389750300262599230122659711207597938274289524883565492856796184837137067774799925920348825172845666796237944019232743113109915690803318695529768577826308869110506644012051737810932189036583991995137853072042516597316853765485395461544515942349821891360359093699732184913574680154193181395884802257200544950515865902965348744572788591278848275750540814164947085483414547496099826838783372991589663094552572965568496918651360055693072767742459049221306496120097266070061933097900251049119832684170960087811409568021356252863806120983301996481682397017060908361473161899890964338400884333023600616145828805096463835279550128825853158522324755383481256439034641822027902464445662909758369839244945166695009240990112657900678169262234128262909975761278464971659506136389958536814861233441635029775061908994228207696646711737,
  190245069689351437689096523474178488781607700272728106350796256601145774447473315383299674479385171381284302066499914010599425358129615653801375185381905129472620315496617217985437596902979464805381951058075879166107389984530384115994711598004976804949306189075083653462119292489514325873471075381163606624680501011915388336789758917521299798796442047196023370748269253960053889487983786607347337569869405760125861080883494177250867782862288440655668629898246037956140337354514082456513961025897451632758978127037311827372423981758111770365116490640217136181520104274086491911512484954470176847681355831838896379053888934803834098842747338081306487887889317219541931918684792839258631019838794832718045278657892257910886680754121676608005184690846136919995586424161200023371629624097402519335643400670130177665886510443188195075805676114679766653536021159640695029043000038462490005948134527647291702517974882595111540076767259514497374752286117101596620546333738380544450392971007758851729848472232795783909384035514546390313153285200934955488312825614002136412011276440734118350428447829243885781006673500454193764346560120194099197138095489854697291376090288597333984703172334990280355833337156901675226853928067143045995035951914213373061287694843722344086803914994463772034509864296037659093802038205364085126602326595050234964699285344331336106903837430187280197346652566184991292238485658307788831616123949250798768343641449114956318924471064097251551027157369530462402354798185420272752991111871242528069278321294224782613124662396179282218734216892106184530800547206681364788785006263489993795060050562367790069108855354072979945622577932065115345665593598170034605848080456803055359032340039379726486905982560471701355372638461240490261640731411441931832598427537045388847184356908406257395889907283878020069240211236928122385411104118378701871967122857588655238036279995856753457034785732001820879828802348412328829003377658725815831708752424079395145216651894514109609681046336594412765884696017203233856499729744610870750204179764302686459600268753782737158447824560135420753803066044945936601736008160884863545760924244445338562853650444184000530401324869464874643329863494321540788279438694416165539350858127882149834395997884147135294039675125136194700230385533142078740305631956263286789587108669937444249749566374253075655096762335153510903479505554123254517463450558412536547584682557048434589314038191838440819327529082135159701345258406934974803603247232535222414922281174442251198450862612317266191861344194887670178705621229119867400218901744767584121657889823899866295037981874932968829953524756790272673321287095143191882992913079892964896898853449491949107347151281287187555298583741359340008426983263120855590348283249242153598758563933210648326150126046399363189543598541223542975666901843362196197761174230542962918126307509848908597851207136017748426363341176129883739366888760639256028360097278997766156040287832997234732590462683541691953350187273566290596862451110057460511555708856687117342261717163063787382361130207427018098550843236783016884657749743719868259296364309518580420105193245546110726374580105414696118309559983235478819961101035436257763854384232258571602924434394868025769929249658867032312650743621809681458040050399983437803018504029908983818135640235450725595794529039201754952278776718596165167710703213237084557052354408522267930035563197222645923832482302157722990250443238218494464034576508700545737548727879956282799513638901038063537394757057728065063633658738662805375319547842210517943483262600106593705522656052557445284903231867648762434803086682219423336164258978650351850443236340755789055022060520427313984215444589658808204755122554633029656462372263173039853681655448527763318478069144764212059389996682758972553581218782614528289508351012582899278340723743015682295013457282378596595235848033458651519267941959,
  66131111583718749141947408053136792290410383948671995242051466858175570772103636433646007870176426292989301600782030220334305605822638991184977286668707544173054701214905978596618874395300316891907727964915005356397315227300594989123588511058537724668477858077639470050370658819164282787852923607938343824246326904140636656212813100637270537185088569002267442358097241040155930527548088120386395554724434160216670225018178188095261762781917809102852183302518785548480791111020315647246157033132378343608272836950789572388218549630026916007603409740849664014187447601880669446235519772771309041969438600779855659681044380908002232335051894215066136688187087896887640916653839670745072832675211551446493006248747311287616128126396292586062075729241426346260901353661126403384589581252378085377738187384686394092853579799392364975124695050878762556087820865042128634868702201346791830338487413709789020597463922359593979707893537115476161781838121981393558676842655433160666586645106182523812425579010111848049326137473577059941578189015055467191392684755614829911906930283110802413970450203605264071284988616247164455307238969605049692548722773206330718487182132736814587864107071363268764968133331775894936806861852599408868189595287245833541378570294426155392779662858436959951761374465463530343364057074575440407018361496400173301882039014629177349475262949479381857750645879420621492158589769741177331414817349895412669311740345933168141367032007540133529878336502088579687239544223508635348362043367357573822299067015195291880247577992070125258687551223697922368731220672128206056523800745937876557026287160368684253960943166818010596931228988633116067265025976700451690853363600545414956328227447683495838497115857085825341955746207028141887960801239189671191673017874779938872723599574522594569373565806222149439974540987737718646045750279589685068531812538789377979140988796050660649873859785395439488822661882158562999888385957052190012601373831117833010316111251859697362684065680021536868903761939114791903594712090990469671188350136307194704204606887306500748603306106139361515386016920521905478106703432565861157682314376859038835391457819759668556799342280395171058360687401854526198531097313494561347510700639683409529224661317684823627785574248476349844677685918680060863306282602191007694745058874603262920488250192621665060799017679154264761926969256443245121001922211105177320152214507383937338431528196971356913282544977825428139535070246262694089736554195860418209468589804273015041971382384524150701026904548525078648797630663030918440304675539500035482413161594428490153003990955093618809863227823758681285763308189378630818897079880344385990091254900132548916779675366951553858583784021837221467692403363379470517580948803700522252671049804978119036465223222183107099062757113191026365694016850718756941665698364353672301209284210053516714871929313598678197363034238364147908567011983063371952778320818716896243847022762116698468477144673990590017807287434948880067162328304847796028444970453519426278925469991831342469813106211509293692347433803278475170363544875814801660367606974758280365571859556019324886402905913715171612900538475880456314731960037269459870681616555065254355516494555587820338121761139205724596032140903666555415692515624537611381948934476267642777797034583121940597024532284592797190665793198248749189955356861587668528653046030767758967654637625863767236133274755605916512772716159911687093785026302029990849375482550050512885500431895816488256915360206641104260221230825723744798980521252249687370280361615834550480121823671499745887493965239717529072100071281282862181262767067844490788947784468663481354241253961736363292185371276509799201541296385419447743682202528202370187402147797505290842191625414857078447719472876623979501261572017108746010444510962410367599625701176063004917093281415951726467317291320967045612204759939806490998870357960916292449409104519805165355271983571872871483770616601012115786691571537932817115510397040625921107514172665289472397233470296948206585549619583328075163176577724621549876367288349970252471615763586259004736233987038874659565441089348261019185314166888720965302440068168543142488821927168886682713144014719798048943440237230136017805609429164022918516634453644724326714373740335976245543672797876422063965156949351888550250663169618658567611418123761580560185239605465827609722198296439691458837379875421900794054545941204726330283290374465096402471464343916487457055065260099324113848518762475815977809890319766313133269844855731000323200977383915527586902412635072474830453372059855804518533067567342375755175190355475891770227382925482009365765820891592001582373432330217573358650683292070314372609390857186735864987220504998038072544928450640126666466344206456200565714301080463625009546451631027313641936954154059257052702163438357340965483849027679517415111015313469550604393823003873080940930678732733119782967477958985449508319364547347156313482229134192661971929328016969465930529350045381244297017323676936056754468636429537457076216236705936238173064027554337807261476474642610539004323944915198958974352897738456136030752262275200683394563991974649064736188640332300279853538860370947405409381398725740721977528790559777391622597989759601081548001694107555126742059261805530052270099787093131930894731526480184453595440380771423309321816737505972911474509557620713872817417744014008188400924667748814282473868631744195156401192189709103762010521276463543527092684686706337250980219401237670038684759220387494179155826010507325168282724762610510678097328687041865427069876439504607122458432485591270607992073439621954173448036497113645152124656182231166708006558701705037694277935831179449699734888413906227118911432971808286720633543726525587850742404104570052905776473391264127169363984602005294754453717981697818470439317177792979684558443320998063443824390322962031073146888500459025824236841454516179449916269426883820588384034041661565393212114061295164536366369669324205619775746595947282262933161635187701791450621099433617769389778760410903366092972691940301765897289841770499246606608282650792730288911596719156196480973631661019127124372851334138756256063132196099306471223281930875432119925349758001100154444943605117375169452181153550582687455107595374560785195847382494609156074203989975384905526449225137114173746091415641937196664826685201127773887047560923317152986782148727926459279537573127769951430483782830704850263148401277658452143688212704809714358179722598101815603603021921328964263968629914173452896182121020761509179563999919832691770189774786383730181827833486625402411258145323482860125039937990627982615134086337467191164122540310236595348150385491453603102687893709675202596870290755979742634322003668502375840667101342858215320541483964851461825480766971665250448808409337033129158200591749166204535543795388941453666822824827100937322424495266725369032930031206490008482589212430719935384596674925705817998518231436524609146482155186533211603216913298868322831206391823457615861927817123748371011748363474530059663777211437935867072746578708554059375741137015249232716316906975986151226817982477740362234577680964011685235028787199347812187198005541326141710917937717714477849433525622951620100749090826346671823361944002332281412035474694173639865608810969449791891903184568432109067946533769017094609967471987151657336091856308096989625634609361342482691055777767680917551602521230337835004751711126830199568884636225385590649416255127486712495225221923361362895454503873039376813132202193709944797844179307089527554833979439817592422671160517501486275097123031266681499672500993190699654950406015964998039200281881684240764273388352560125966641705149329869185558870242275420664456169131721683931116457164756279,
  2709178218762596391356955501108392387705194541619624700725333440920110490255239764069637984107118761355216693963331114546284558075208735408062568968446924323736465330326930975373033208978503398586326164039277262718231223902772370910607221457799033956593506003595820002382623471748610935573205824558531580696649522454378939974100707308967046103412244298877595893161437381379778081743447204944248453731666146617758204204638971762296100032860441429396534466263605537180124959792902927082735416982543040123007185111711122234840350703971062860968474973526491378197248609456357161910042580829128195809512852721464004041673984978019010964085946688945481615848486436941837546137607454155621966515077820691420701491471669291962140261885548209934569070333878902551450390566607908090765944701177849687659489879591007335618832578788130230668731214442343941336854915940956725468271681749336511500589745512686312219652752631281297779035647261273464771926683955953116775590173882482186739273372649165520410179391938127204348561342667300251834610339949851106525387802650286255385903362899504784621370756307846655848593548295156390444840042932279923422853924672077986493096327430290666694139300401855627492363071722609778276580217181682364402641648081744126536583028748424448489497721541161447153189268907733703470528745105862971573491592312240853406994546827171805616988184332060572258158485376510958569455567128803757339397675126341075754948239021352394414365595710261600869914907303511918953973557078148730019319461378622028041500270665259519093027767042473053794633579337550890683941094215419287506293624523559086138472076960407396615569171933469622495525694956137799906356171426540118057479842205313149660915946542818272005713222072886944811607885313079079670840105215550404140884652290865734768026465333637452790355608697609747668616867876290539050478027244365038756592580843336718583620768587900011620350266296513807996324828495760593966544732008227527838474016516341168776039768148875843167809750769471771589758803121660696933977790423054056906156524208406235158698889061623565553675965989044184659327386044318633206888174067635684818390174120607421789322060224645568026876053365930567811118887356663302028667569806017925042561666738115658243707292832153242999662435502240679493471476650353351939820416923007207381690185686946876586475282336824616470095244964685078656776714830146408511291431521917788783624422814200298966471305922146970511037830737505276059870347582283160843989968219076730785559552900916352874562880810001755556132993604683996525733299214075482686849258139692585282514406118448323018379612230196552763851589523391099758477042372812450264729305568815529415325012065204339382889171798695496530624867551593680445253714245213755319744801854847829537387874913594658299374197981206191099001911105701594151147294685275464138306101013501390459534113617740721265488788682206978394118558276865138621387207924006256507797085724452109814792321357211128726763805168754778664353972462555729582966875638129113969329878663415134131042734309040282620769218131648526164524395875449472584787741696546853713865832198647287904773807829231336713950551047450883616433565800692445385800339332492322604509469779468890084822012055191788324880239093022392232583816043923774249680756909505029573961410989015145527392600512149977633329860909010514366932162232886451710849465061424335961153923196596840225193343071036520914747801111085947146667111126963678060544356332332947868536711886349969986317117601965666649273379120683099408425149074327626359992721988881267142407337827525124057247503940841133002384224642339311205952061612315098767056884194623037783652566833436499804857008316142120817969049463977083693796134096362471898980724708186143032621932997277236097692974459641578889660986381621579522778474331199730552724297895798063870740949026368321296002098987416743201107609019155452505710437672053421837841920847903191165846478898883008539579050848554463593506795024355236383704244668701010314582311363051303335580036668665382296072994825218992236952170485114155366257592771660996563681938088154430811492581520747928487764870354912113248011187716994088030639263175826273581329575390342101266847042112696969986146766817820234495905499957158451659260973262518132062826152471506817881467789128935819416587793058716400210351606490056344441613698209953345084226098588117776872074990247602586037274833163850061693042932011607868203844664292347533011431561986315289665515804892670359519165773098933628115897565274155578865491171859409759931741182088820886873866824471300584048718933549820074375502169499139665750005419042113594043991396635190968926819410481352986110262725889748546693175300443893770375763581687718833834105475899799911420152872457449618727975495257520784160600325384321316506049829393523489370944607021830795319160507584066202475906274238736990056648589184975510330461147264475409646731476006953434615833286582185632735471791531439689574022937222307091977248399851695352016917469239222121054533798001888659842011024816147473892244219934417201302769399688949169425536393178288070866139260527968951537026176256645219548427022185336688042455473518442887890571710312493325653530665551851950880708127918595448751195553817572536156685446964241932417170832642961159970632312442219519073847945194617704290804094813913328482021555737929577794446371271458615673358502212583422541193325908914990348118884078659048751158893638120309325120070141702270638883331903324376070282235685812860732343819750455251343546472888160876261806429630185423764112619097456291380718606080468030812166798397003473774015309352586807109217851535671294704416162629930772521824987296881602755993213675370301832904427158030371079384173309885443213878097530882762646100019773295691771512885321559778875935011424956159164541201300027106489262741997640741591594703975878006308458598402757829366349769101351447551155634898947437845284996532066000225299501150468940506835975340063637940043693878775120285265206955207075764662387666958316731680651706530515349401616291022458642150395471478090402609013373772899698425463249598692834214868186890150360822063257900407943183469014726843264781114927948817167981880486808515616737834337272006796616960369829117834167867334628125131950808966038239233012956675453181199407146011557137275997110048812692210706773050939308160564186612664795347767175956269471325000447742526861331859407830924939367193791447453857818176856922032520632477527473129375834773251252591863431289656818790556666398606321389420002955122945351618045463631567050916680353897052350957888890656806607722827121274792498392197767778389151807763959308627577849807874390065922952515260550126181467696654294978862201306355271028392645905032503259283657473910974204434785804659798876124556826406969153911380332599879777593266345787678829558119960283136144867448765155142704019281135371825113439567038446797894002820191736886517636560228169627709443479099023505385460710499075104561740414792227123385159880131796389465090241270836976734460817434596700880072033434824114199209898115685045868864659945598972549827265304458739985965380845667187397636221752540872061944062747528625096847837767157402624321452638808047179261727693740256880981011974114241340393133902690866708427914780351145639365048991672410462805118623418629624137347737920718808204157845972276553912684301421072541410451303007488733368526048127050144311127273980680494580320656953762053711046660241604979751142003173662692632162956209927574622689417187920716678139504971606551897892112441631659827722398223933713087084989742165111551044559793838084560873265601369731015802542028269704409043759211291629207967940128142445476803503152318781292512822625927939840700870373403078136633351197936500534807539647032739546600528895403329726588587581710814490973420068734825889111614905076980300862797692930411415668546269584282574359149915984590779655006880006879389574274671711640326606601708843413750559568021685498269137421042766659437323141032686886395317995672509316354303084471920691994990400732070984915393644486402042886529445367118399464256630946220724440870980961266564460987096724544891602229376015484447674524779217119148365553697056345204212637845866221371810779967015879846270988539784931320857366832391297972149514995081628064980571417711637673504320738481256443882893543721337032590906923136026626878927131694484419416836628864501846644353793055835786041869653109596777516129353812897723172298939550124659768193841667631885456812925494070241867415934980105809984752231605598264547244319585978605238837644241336659120376717013370990168553267546706580531087148319947742599540902717481255230311616740194418295275744874197556133695576408981992668459358165311012012429294782126068875474568186889755782968020845266634237864985104052041114218490316464798232635690596382878205066185680861762579599491460425650940542298072708034255847152052820250610331872850427289473519191193000716795453072182305770894438196546035724471827872874955311007634544359807323824362637170762087958170075558212457043370997429375628722726945932169151569056619463235458788402424906080217416194213004414672634072944803365996900123657285684827578892426251119389569775320723626074951890347397385059244632965458168569014079807753055330289402977954888689007234971655811091413830835629813138051823496783710176490962124358357900412276062280424157817548415795738746298717469886250012337583982169927051215492328104636264748041880489023251905708216887191731081566773590782526585707541986419243204771030198561689731088914242632320400039229252082868534974756463903368013531291698841913105435253453604615540660315364465113852664644619320323673024527307970243544834093845535966099005851454388856235210234886727754366663838074849719625644550695518144019636886829488472677605957340112541192075473269903537120566785856225972280525173915271001068209475253069678198310010608055903721439011474935883159215396736078900569237443432874819755672626847045429705355423010804721960209908006782994003650078032768693564082187893937859153922291017976180800168786498198052828919575174357575736575472830435002924715357907400143280034262000775363821963956427092456783021939718837503844153964583638961887377960298896600478972612721120448100293813377868882037081458708859236105100573238192330030226675905979550556030889438324197074220482235141719766915168967006534930635130311259698821992694955940070321150232285894867715601421008523657028336645080529906373996735897387270653022170920088048565021467292496248339712839719247915634581152416230360835168894247609602365479890551084949614022209304005389584919823197103619846119377304607659868610400897721049625031645079945259192197927374914512107759720794559496253368567830906071712438229433368750643512659154519636302849959154419385572968707559690497283159368300112260992737689305845013827792974434740231920145673628401982156543051910573029153920849354958048885833593996947754265295011495675833877934800947259473337912489127639237315990786601927264544386987618129754667568436170833978309218811418624536356403169185088918303771280450886294109745915305729133551992410019867063753356668680200875929708457387512194134360515539689744106188628355198786316720701629003116513379532238199602882998869462765666226464037883244106874052905865161764650971317024083045606000871612804058280773803992055488390082208475738688347053589905611791656307311404208578780425271276934210804179851877654622821444526521799956605324829956349029609015749900455940017936478084334242725694633142078643226042832569474705245895518106036480092804486885742008644118774627943540592363414262709837154574016431481399626342002388831456961333138102273234350587173354389555299313334779461826109533884158906385480837506592124903966283787474449675301112071020843758207136735330839698257832092772198810696370899630473810725309996102199204616060176229264252783238378523870304570076179093438851617736055652765147434801211890716831750632033226385518162694921658301360433795786763599203712439869221370469209009754962439197070940506041671186585109411978336039200768352361297762940494637439854205962666470935687106636644224425989917322195872093545536144615438511097238047321367981817453051381968493706273304874596866661643838102552136954774434380892595689735465933743611120533381198681119070079551375537038879987357570517496834729261801069188030062245247258803734908878599803455120499749780055087928511633139207969701545043832805094635881206773596931216763581952321143623354775671329224305050205625487071917187145593424858327323597608216629512650516394260242255850995452093988442087792737940439467232257593772410564152927599813096990217113164148937768841100233996466044183803967933239156860332144983344082746014234804321764358551282816715452507018369513568457794794537395830665682443276544469887506248616875884683023220029975111198024062004076413333456399497424718084437834488420110112376677470482595788781670454984493909826180515890539860892411290253274025842513075721640682778295369111887005955591203185017935853315254937698764379660867388867535205313225865279645803975836000877704405647463049498160506860211750695225419067783718043293982967485427945326323413772794730739490717299356416722513827270815023400162963560020390227782989296621749077207894917517476215614618851727192858209366771224071240524828604141401800672747255238739247423619326662664995377779537754433517237457977559078490661899000428310615049093635519239771703757133903796956545214063311211084839776304909061358764180830464004246865234768631433214310032557336364780300557474549284694664215013304538337528775417753338605466454818384547392190995231382414813543612320884838658966600638301504580366420410534920645324995425519086609758448257503943097640527487974327199868205457215604286277740896085740279964234548878745974869865201727423966788057230269418483221220750830433180267290637129510157965254132619360401203052669910645542950459139915404439306237498538350590368985939558733184176258676558459493299678708548938810325433170098954479496197305916122753709484062921039673909628272089178031227475072329258173971696249281354176275115937988856936505141010987544449347322695833467161320827279310316454497873379536860847324243297987820539196898331175995897445423364900063104819506520365867536631697738130117107339680099837031609514927686076632995278931233226820248946605567868480993859034239887416552766542148636673248298873401841015996126317638069976235139090378929061585444975894845446497221223013128782644351248426892272932315621635979754718107096149724446970174506597772641553912667387917708291692837127840633564205208127053651941024961836642207766734264727463304644758213637236492634274584414179054178839073775335486387341351691637248930107475187611534803224231624271656006574499413713738894915570049849180199969677989205700259141126418744885562562524488991523366204230488512645772750230438915107898277654587997922257608018040330306667779881883485900206457840881796040984858922091238564904575630878750385013024699345527377555711960854214608631779052987657793587124396151497888815187399354566875753923853544320683722416899891289249191547183404860486844347059428426710833323103984857665183764554121248942533366129379760626432693897405284844341216239464499027309696735492773621149262693656196995266034734237895653019496591609097096722965055221016125396317721016023381033226895076453684199511764481025276074672583300749489428553772029476132233168793045522072972214903578962827735541349170967694800929859328578955226218267981495652617500215482916523667491479335218565919228080387182301853887,
  1607952431930574308967036505268849087473990330160811845003760975746009892270304942788396873233035039006991164922200911260531915805830800264001050189713945685911800352458524441134481153132001504101643900966797252634617088257791507916981113441892500607198758173726773009840728379804975789131145203691117730585409417308368013983841032620233223966002616595748970109161109750460826674418889867310080923587968840125694962488133915304574495247302098266548341822794475348212190838742598847092236858222845715511080680775168650032441640065440119915081382841939269327798374445953441337602387040650659181591970513181189624200618779896615389792848754141098598417550406915991965673531881692426567059861752015620151918782202818785335450273278873325541577962589293145658243228815706421947994866540358256265413292224018995262583796659767748503584174042809551656909262795966703889734336243650163285074126709092464132683818568112492056752353472158739206138684315231580696657754240842106495137835966983234339028835473845788750431828419625423270132637392817369582200512007413717154885368575231296241688429035041840931620729697250999422366450647593057877934268251252543200372987884309923784168862866240914654883831935514378607035821910287197392645305302794399051976436085105362815879854830248783236448917010863219336031946541561346779574687580522170285911426532130085759508375066541657425689384679364244951308104123795607264659531630869905609418533015119932786395155105353799180909707719447776893775839754695947487324603005343320561071805726043763930078148716065583531779478263459505239420727107113193816411223813735948066752614700872204049261860391449968826592412819077226563382223249849925763751960516162602234299602932707199751795319082104032114641824331328878534736720209797474445361675201016362177285039572208652977721886631146098322583361456465530134050873737307926550856275467018147100871690895545622597144623153413362899661744257014934837512875402131899191530008767084766858680085835246190584471927646524776343874287105564938383606840732989912651965772729187491892150210910922524777922309079651614058465752961066211331562626786283862135690954363915703842987949117830464973539193014096795626979690110922754979255973834517510251395464149275978125250455778230956285144927393092353781874747032061242291811873165574295411384740373974325787775091758718696862192332253345533918354092035706903206913558861263635169858577029813027744247577282275863690213641374932368766377540532530020021925831105021375663035081052027264141596586103175968444777003856540506968787808130100667577001868225182933378819841906631642873055974083905105997187044518662452427897444727507914601204231300085304929423868064524770582758901513716571865977958567674488933710538371106720884504277064894773703963453231325990670512569962434845553323334179965916429027892670108509045616218900913511730263225315891433420665242627205568697222302157569135397412491878974325636253856385716469153411442115127858302066764310579465835158773738541405773156914109752217494600683681657550992098534685707930570925452953517739115884228653626372998138841262417257724912665528157150472573186138982457951132669383484310225940424338555758310693406417234838768086067366551343151960604675277709636919061137904239557447605224805177851680010720689587288350150556823712409604324611170708601193408256780789181174464248110994226840771684696041717536243879893852228846720039921908718460331366077402121032583370969803201027206443476753634951192905661790870381269488599652013631035879060257461697567064221738639938322196549452539793407539916550175422808895687332206093327387345989911712359763503980783515086570875761717436463202004678113926665330862384514908480155947553987600915765274221279968265828808221568482319150710546050823721685358703700948037026735992918446866307374101010941808504761265964194951474336418599450425716085109088648539169941436365317515333035037384752217505071502981285143507916752991174552815129838428436064860148766707351136991550773849481438600708564425365620836998661914281627782143462417827685976609026337509385451051370436445953369280571771163692852659225080056542057131201032689586858175684576694640783528162741044255454668024505177082500154719482119656670981388268687972070198885154321910215921170677091855903848883992899464432644271047748260844799494238683980525796519916630317903301096253888434620734909867041012446808180986991038806385281262271444157985669605579514636747257752281418199075393695661871567646921340972144915504279214840980013151629776909208873591768243327023641610524163988569104995837551956700882917079115853910036394604637705274643521799027118407299136372251066538612613867822112434985887272314904805585406984820732626067065862268741237922657777773727099377966055994823538856392714023963195962872067201561203505634173873315472071290875130815615928558098394237104984268394808586542638353430078456519822098526186631136070617881839331987660897652867264264654380743875611509460816574341931530386465552474884735208838415231944647474384013247655881458846012707354568178161148885772254851873559994896970991436551675737970991877266112668823814845733256238762766905592204473676815514627108820030274716275077135363470619331458125052264139080942024527026885330743880661275546209385945163323576449126916054397327061853469631710662076642268385925595084816658275193499204970277144705326349005854794290779736701444471973174032510084410418725416956114450994115481490377456882390532605151358820770632844893444025928124382378876408241698813435227843208527152202646200267062026711260710507382285105601681859172707715469700095490159458271364476002469781594898034861894550712131461884931850739073870245115873693241433866777272007687886047619712003822724870626774500915070269916074294155297852996018962902709108493036799993625709321692528332113847726996744721987505411941323235964114092678677537682363865788765179023160852179062794413544457810853696955550114290390723977635187269088873397381013107883454252798107421768778146882389326768725476806512615203689121119044490516677872247274010871798019727007207438138998061030298792552877004362543164222239331946453948814293260651174234654126833421761334662084475035600689193970744272864392701666695923160415900831418560395758584374343361953830076711335099699474844663974609743310218310115818008371068001378068762177353776404664499234264916091731881510618668628577010517985083141737166766501196690673285327555084536315746768078197357273929192247836360991415692864781594022635019065680012734172350424935436534169906350952540764030406453973704231541337712703406439169122273495832678004494798149973136029295249168118156227856170505780359546683153876938460849219497915997609934420933861005919875630482595922438205133696204692749858413510370343702222167765836703194138762132321420359773563510268057661877157662504000911951949061515900590962453040451031998748332763863224691160132456597381450386024394974371007147097869469008702721263823869784059822515615813547713734635366529357529760961589719718848635423775259946855388999315283201596410175966969502461573054202198608618313413077514870710017982934046670734719922318739054596892879821835233008685136943112790420205713971225333106470310548175062801079087775542995198599190817853048364891945259460252586402091378892924614955988736218603157384760051324056166973295972399393032165713761014578286852071388704386797574114919969723773651467787026148949954261554005384164155054971806768895437183842393915231432395266663220150450856952662936700174225508519228400596030822531248875235899352950434851146157988943378829193515045677171256712876794755149123943270261565207747090832513440967519576478775525834501420121342450848088763529221595208084311138061734296237092302858266359801741754886907348077761552922524663163950908018004119969069915559242972358087993995200046000890844423906027724032905525564475557303039213569270329178057759503648356964997806617722228784216111420438561196254749143826583958334897622633677407674792925417691333124199417035367858917990988811497070587916020011123424632984147083625711241870045503657386964409289970284313333779108493672676888438487582346639381668330445169146274988983324957329741047467391378008986855093047766519462113592623175399646949351523832053658136332101409253431971484664085373136247064066499170695221653896282622825609976664873915332241326224643044487255479680859896594251023909036180811615055863962087778134173685069404258529741918395100523761143141566195039827573036540589270201578937722085921697661552399603608019902185154344908001887099905560430535761032870872376477767125904080992904244953345968567610446447430528931265326735658413756354155811798911621918921920225694135357647650101671866394682159404084059971290224906981983089358348478230086971045009245881508276851008291943908750450491740125484563678262563591773328659076304110935045572598669983345690764160084541140953948168130196753593548767366995746277994185559846878799163958518097495361898115454369772923613565168721665098857769332946688868442163007009582124483799000099513021224831071490768818921784408624928559634727466531428181988590435356935556515560557897499014364571546622888332336985176379063419046146657423601318875571114134051826856778784844933434655866207125709540910012289816067932279769982693136434507015040366179237194024999489935486381260985473902659763491178758722788028019354621423536594476761034827726029254063819267814352441831986277728664526667684585100818214464710216576455010317149567995617317890654820597693309159965255647915192344355395665387924509905353018218609602442838384171430166815042998876502921561973287589080818421520504405850058838165346688741628672526160329597162362616282750109725040430813277615512752548008389477444420278862748721031976110289189020301388466808900675862663168484791512750170570748621315445615608702185583876303922596404676738487823887311100255166628291915875091220567756517866968353872063864586318908938307826251981890292048159049649167080015755542854518019390120579956699699269105536933619873554471975261552684616355089494142711166597515058968523930070955653761619184033040753596500679299494654994396717285009670735168475968493579322176367766049439679917689769603819836180079254278145135271485049033246732726897932184819596032971713819963799769256139955795464801689326036437087331520203349691986442081631424540141108102721100679012658766428782358258431167757889941590571697297663830457889213728149397076332279559524515253336075501194868119966991989925042837062299605108285434302380405036254620985205453929602271490744069039852409557354223484293139488325701224636924352638783098016206394938506558141938872509035201178144161580611163907362317462002810747748872057193343763338492230805635497156067671365095593854613882324631701756519921721691325222611475479560406922534419769644664401926775011484744768071999062517358368540574740667222512709307207026115752361420662855320468849160209381502123190309966098827082315552430325975868244572273320317058145747645274138245106173207864610466053388312912040537740339713419262679908345274424382923686910793142522831911809953840488114174170209479345780049605758142341182587733962414497916167352987843369813106539776791924000166029606392343618668024170981247282664155463286231280524372250407788804569033029496085232985783442141561886932048078889322856398491393016923771473014035307663784469673443343263434380999332583113666884304497948702950702386529953384656426588110004368007171246610787847980578034415856914774972133938457816071528176972394177427547629632305637126041200012589261484286234045111750307466909921157054226179319687712145995906906368094226445499821169034130763482528743005858418460711512687676496097432714856685421355130245926670097679078081406200922452749870631127569637026755190137557201829388515374868712954300698404164441019569060264063643349793919741417019006764109494236484970370641804141728070829186952200560110759356746986250096251639567106829874760184439765753188408133738212807186053569301111398107708712960451997472222639128979372146513189661328084415500909172219613863225707935043654724638253126546209024188326323353594219519820089590257232426874427679100929085866737512394775615622073423684960590912775552107715971673247427195413274245626125773622946910745925420784492285463533310970288132457283715087971007719190544932181980168283614919474143140582095154982579004373380781984648710978457453458945614214017666240228640032033556019912299974581057539898637283333499273767737532989771482554134987447238097244991017795825350091220332914503509122669636551011686792071010000336262275254868381701016839986493822329694631257577437593583861181235485671531485286190856364705576288450991628905695351843835292042603918187455651942115232745571691058721783534517276939644884893430629732338334774622299336609029980940295435897234605798514053761370586775386402005526856655146964905614363747330904814468817784985214716312983785670284454841777459848149040366890823130108558880685161731637408073957052797093776435260698598912615102431386540168649163512439316456049792130756509243586478102963393875632402155664238403014639183093223424848241694041118318628796889878581513173616088638199499276065454882738024394539851690489443502938914933020447797548695791600489160472658772098458877198686700784918171959021875832613077496307574207207437907957913289769289575480966297212399630515227554461839461517578024756129044620222875363526549579665471220414442197760693229303645879180351708145562373311305325669389301118295954020646077872633620931544183010344953390772430966329157760485079379069371732360043458085591183266243981132523546053378883522446963652816960009674192959614547472404719543328853670928918884305727253100177303511615877440883988590224279807283516376844406099392180465255604775770436700596837047800175401304112848560379839066278824799642117945248921831956553250206898948839183032634956243737381265198055036507472747674729051458152740162799895883496050293362620358343059205901837663129967120804487920359060783773882226209904682219580636848744695481340661619842668336218601520863939165393440871549398257852728163431463170975158479944360249783658523044510662191662110748070916700369597821061383926737088588587677128990715853831652201458772086346742440346437994808590229325208546382098860769330752464695863966297386899990631236208575912977758648277163940519322167103146764004923685562892278668173059487231698316184385191215874888838664323248489991260429192345834970361492420274070998273061332343297390773610622328043712596227484008651887952602381592487826493260436335633154287761776237956742948750435358302460698334867290328280160545485816710290904845824007970385061041825671038499948901941094921557032270484782910541866625819237010529810584282876896895631053624257396265055157076767223211153108020318431901551734716953408345594458890583150431738040878144289348621986821622801819777504280624266754481142079955709370884812177123569493812065868005306809237941306931195785935271443324570288380340279630749323094475883917799302435795756441678277213562754172939768298949652331863400932934719242627427293677673208594254459679342001965728206717819009071725952937420036570751937110683889151146472949401580642421402520391168247081083962896701844451128033099971343225920853111347098234540147193554111180761174155265970451086569249312770312124044553932040631185506949830732310718147998020174753288744990827993465590410878301279117532911508236998007486145458686619713311558986902092516637028624015498326266119858574082988939568667226798198946182582448972630937411475668426382744244248868445358800150296157400186513038186781822173856075175040978038015439685407135915568324433614074715074741721107643826690097629680129655391660505126206148559550535630797314087782518854999121164632574919191709760308023427322230789612829601255083098388929388421783194170762796002437320213541036049750859547003661732758831441554991776316603863383649179695746845175338752633945536583443157690835229673267784493012662718857007673486741530108416903911383131719568755324997308243056500736123015439717652383483662860897731081732507928965001532243179318694671010870061260739612055806629075443477822020404779415670964361803750452799163956893174968701705688667378638681091390593866242664718373596598210027831012498265787347644086243374928368371382756660139063390092953183895190880236516410182897689305247965603444722720399422126106370831930899893545262559350242296712129397639025543810727719049039864834598765420830312688441985174464647797864168563995726900366959329041239503151876585435358618343460116048312829249614116367323303189277636532461002240343667303597749070949592448951029701710011934195232701004835767659816595206157501231304856366739203980752305786195003952621068791904143692087438086049562502835031600751780262217340071248804592973444740763310866855938622611778177858838811622349445319733870211282247620324441585871224437875191958215547858348413117577391166036879743109200375794345816215606896255248988911821005148351270515671377071362315844885899018047984484744114120172190337431359880427735751925108932985148533144384025306949211524283660407443070197827812473974343464549800671249485899820436136370972985148718590672151230739657693562078589530835005999006059235917155217844340688052429269076806495307689779432389408220391318908175626082985896276097387832623109750894122679260483049867969168650175340645394259138591469021435139210428028219696358471040649975311879154608758636871238943771745795425121718220411007529183918812581434306657112238937161155856118794258359311334503512066103023491022667590125887384963751743223926330723586554702344611141420312958941179721199747505872568254737857678596355068038168607988545570270130301525662044156092304441215826832248686847966771382271648112627683442758728920492130687655716718300497015885483242971207898836148060627866865594189882447011283363245324726968994909497593732479542163995570419682966370720449873425229487451359797678298602384543278431986189379350089785654951948804323439386646530564229114913179175190331597202335148282816019041335238555107511104999744372228888489761873678782360004890217097521629734597688991262005291668686275901022024837130719263944449427449811831283545024699256979048155999653269411553277741027432078604292594463977268231740868213796932487212750570468785330164567520697606298646961617984654589576591924560767648226437465285548103660290490131725476236332777823251286692867291231329071816766381561874398287920905518953526487854683793970537823191998845362013656310605966928278761578463882017152195604257610699182684855651800599341601772665976689236302397247366993723464566335222087515459928882748780666900240077379115380932153024532485859513287764995103512859645103382542976283767636784785860393348877838191126670060925368016257049049976379152424705832264987023306284473410030887355895375096580431259691225386562637510903132042218615902571886414179171132680778633689197735029790300803180708984224769101678420892712577050148051100757820179607897178394768261136406367045148591231190117975988249521199651966874234060768952181148605097606058721767215427391884762180135499379819842102674499812087133402168579448809559446294728243891193916030013450043693433109158341767665643816950901174386551062360941894825576641092949504466961528467283980218551785122854212069959520507468154782480167143342579386626145421995940046576655887291114147650813714025781394246182950189728431060188143370241008329983258783699413764828092775873632014263706709725899661408763018145436899272935002626740893612907834669161569985944857049065896956610731550683055526475710224843940501982119838741698086519346162189406151875804528536607369648190277379372162551145473933479747881565835322744315463927748961653235244087593459504387013881597124017469123406170989553059617354682536960149490452982672326490500181905554263740446683600868476382969359882298552302466338247278054112445485908490571069071111922164330755964188048524160308513079394982823089698275516379767756108706674754086654959452255415883434768987458191015847167571382942001923610192020013480048024856772349450341650744340285436334827265683299623927196516127107442701032260485373124015193487203397127473145345298342352803665270386566258863592941008442933704259682059253669710303113308625620503464495016612129618478174336480902948666257132001798272732803507913532843980151597029922990836611580533719787735576783457310398106761145645615360767683209665274495019865572959075426709013468316975896255241240335725504838279942244602336233916760177896056489860675046830095943228787902865078839734314187755497360510854408443195065027552292391190940569154462105564758776505229186140104788236126564061923517902641970720870149136603309121028711971898379868193615115449579535740263223948024810367734560001146815517593067048991055372795613874594199303635716038065181857079828721857094348599736440297808143846235543106748823504182703802712048284880896911382502774534612762953982499981793904509185757322876079748404212369970772222254109381911106208338232041660393827556917103537942685944575232045856308177212737045649657438601276724221212786257841553674872757392899691605962580530161982521977770325402421862014254656732300389149789178509276368666546395530909500144431101461086121949637414093402704058686408303842033306733016880823190745038431515718306587121461156926744552025315741888888273407758376523327244218281983572552868270542541662441106468746409519546855589968468590615771330712479822009149344976788885797731510070248903085450884812475201523284684861238680230851244542727166790467666759598141180822462617164982710468437177113798421146997651162905929777408666869205898021498298556513188526460957659942275685323068024924492048979378431996461358902228948434190973401258357528199729730742640641566538330647376188287585982953728944999284792518380496472963672832517297692424870246983059608354814957124149310596730086708598301143633568001713161448617057319894352006614436958481361061274233820006763667038629620333078260478699666205872054684245943433017473737712982936912838387499069867164081946125461350806936005690605162009738976228373315191620215047743250434008024919331652913612512345022848522843432524308552799024902863764509247821286736942743279599208152258438613167093172088191559217403660290457315421721242161579131802636658495590740836044232589629852514224607037717824510138344990014626706264324439796526707777407442516527817574743257050948320336491272811860724268583581198738426240137308289756296078863836453396740171016618997077806369203855449266251710400120019816327555231082671386927465795620281927060668170144326001796408543384318570731274485927478363247980448118657248639316519713815179386068342965081317308732676773449546840817446649528766647875772972055814676000709787647553979855613788783215151957960240523377677253315533620590616398594467147371764066725773491148693070643213456135539287463146031661451508614064422215660690659339973593796575141703837764783651131331651852283733187402169680542465761201908011083587819249068479262907181474236859516974278572253316689220937932972894557927804131267809501029118877187543860808988322292596880641274007334501644146244142952985694535201960646131254156784592383710669764512394774294823420830269683129322668464700366351130221149389128893615938479690643328644444171075451504917484498563230865657908705528431604805113099700548015844766910091800209092558670339968638785540618616266367416273194257970000916604789452103027395128437341443192481700025806432805669007855633753121534603844221889677195126351908046027514676582742414501440872524349652578831123267393852419280417928137907321708646024545148355799880650527520160878727688838445400488303101768543367804515244027635095253819604257256053532716627038270822354309405607079067606673470219904442985053771047169276242295927000429464218349355979385227537882965053639953509191926055295594396072831462912916706451957474758325512386604593630000801714415101972407324404084455121617810914749854274396493008133667288970757536285148641709665762022852246853580441041938715486581994201960160884013846779696424145023136768056714088717714862005664980677712672138587978772554783338257400534617855229785717727734618486390628119063685049587569045492259815069748924367746354659225762040991060994606705364154677569926282113994710541290839194641622296608082261867330068917950186162035156176384254345911916917236154349233915645624106112309581157930969838410818492450435875984491537768399179959606607143318451651272948928829519227953151535398390146952151506255404946732552240386840815153092735371703440374077936847713904928650580298697551678641278232084128674252948514413444335154327994176539186439772109289452552368049490905072211326176007266699110722991875692885957160387710151592618018668241460139846516906114160071625979583901797698762836544201058199602370415716388275250051567699733174062699284526228461384161526341889678482877387348542068194127348836063459871789183436131321857705456823635307034610560672551723952113823633148346372246604857838981231904289152534895179992496394927540383992706855163283438009955572465704887526663216165838945454132389639042638306274887129729018422925691828560066386820349177583495124751827873781715777455870473976482861171309706756926728294557424747369171039446167561640798583039742095119833502562811825516241460369580276945484180466308628877960259763283944690792916597663619644146506480155219041231268915328957345322752051729981297171520890073939615938672366054416878858231321557198986198835319129909596565470791337371294332891584747883940746499553934540791064217407553908336035148458285975852761159158511882843539378717079532962071431645298408179158874961261980003499424910988534920542888746650408091888021914477384189874838668470839943337034800243085966587786901512597138104507358532656072239285842050693600639040714332806826098590608255538323961855407823666158582355672342619849678430454721271606595518394127802863137952927691146460352422896997591570609564432756885045209506549099237558334706458633640118902940876729826190853555752291142528751072970140434987529437866831705932841750617709344729434774525189906123513617878576555225224349241129725433561941435456514811863282968300532594448490550736000861172056482362756388576986967888783444077530896258939925252353155050094042358789494471448139966375912244054798865394751810654096024099756123956088484537986909558133279560974045759631680032128304603013721913911272315826763429038032720768016980190281241881658309283374098238070999198201057644325295834033885314731520527217323861513504348837483065237015329625739752423454537741125249738553185559915379257971375890990182644950562103664892347494560088812075987955265371560094968861789958461462153262231074831098135605452710378513731311646235799502211981974448308580834678225101454938669282174831000634137751997714242522819354072530616672364657219515632230630695650424714083296706505797905289068772907379992178899324420246205801545860178078911594576457652458227819060812613573458985503586941247801529796995451374796848813192175028390755168470625035458799806481475708987958752459316321113729771524949360087527708151827336395305696545124175105440661490973501255453288603304053576127169944500254924184881205073854535834511275181503225684213421160900569842172610075774562406673799830705385368738708855208469847780971212588449786008724428082561247965908705079075582420556156814538498426746345123412624351233636408550808173092709643306382123752681096861918898764521449568059002178640858998594781252513255119525308849186293352654839614003488334438566985971225990115959095395036494098967293010383163638802324623140271687918075348772763859915394753842680048607888212045122503888451870929953109936345852001466769972075863911404215599451010187326167035973210859099799044114405530905619695599931046231099202644453792850184823868734928549893205989373542511853891943150308438941732033594418785396749505821692396947265494555576497907871144453690062469530953089844628666022350056252226179472911894482752187466809438406399174698738703190020353884227100294679116215741891419664070217356209999966851934257788135694946879311028148382216490039894429197439519946640125514323592593267927943358518124340451344037269053846746528619286154783358141877145814517162813548201602632156010494887486428213790545917704794431017241694552999384387827735677524904617682822755512926419302882485251114772077953057800446323253189201815313260308642064396248503972425571139797848973413579082787330847922317674565391161081702928725223911915381366854598919501830726274324965281340804360300698284839651887865350518717357317526672297817537340132293969745208380309737826424842747359380408187086791229160139042931943511411020773190943200256141800744881242009379560738922812928767680135396524576170024760409972047475225509607978999562617228604090894462024939413572477910759330197777954026531704900180037994984265602468858914481281709760144428669055204441567454117863902607471406626836719155050490950577814645272605721001000290637756863531762185603859506962068304285363823719921408093971890229571501435552475073335188940880395678170270606833155486678362762498588953682920617166741376435861585459398105863718611505067378050106625743163967238135537758347081126673800011835100754280982587228350813266622689453553063040522148573995965801648076127303639456332964464129275531485263111999042363104076025448022940395439831439330900446498149384004035032105834132462048195781298159313971751444694903918934757018589878984592592740211202524194166615296113053900308836275965436003325415005052165341089651048489745653717284706324368473652160707660895808099017126581138035096164480810305862064952372740298512442513795025607269545871507741175685782562505237989428381336546101794605469687703535366499199394759731888732239438982923500256667672812012254150771122670834482918480766245411098045286499236215562585638230345812361021598700357568368198291787641224129193420546415052762125736447959601957253577514579279201008908321768890361374838263543479731040846411699516608181291075808051345883591772490965953429344826955318622355276938514837262924816951137621153502443404714829954164960093786152968046943765346591315272827629883204920902133186578217551054413515789613514816504841072518253798187024723286006820771000346288439652901777315591441114453401486445826116994583215558811055459930788728427489512484478802024799325669709446037352181212333449014703062698267365184557411867654006709059411391532669142662887734877500257043413721822081124008819117782476440172747073477769988017272555959676654974335764379700676919911411183261341396674515790409158338552069636410917552480424202867842459305979338946030772672502238125675713437060962903640249207425379728485563850335880293179941778479730875842883189938615484104301307535522056474399408089148596246996784705756325451016659480435434705389183867379341398796446695714237574250967986914133824610949781962295287121351229508051445994074777570076106005475971369901435022052422027468477774601952807485786697883428124782581673651288313249856657314091146373809541611605351300114281890952691939046665445897646505875113449360721514497095842340723367071107761,
  278912001644037475278922286539844372676593144867561758157596504490229254514027288900790032520622762814839501214759224456676783906468229404612983737371938103613793081056476747227908788699877415748629697480743740594213021029942385421207162575796288163872233605115352597176175205484962898423070963459636762849547249646581272429051989911538724592731099359435556225491610019537922793323704609271982821102115346194356210812526553120048319253347097477497494784722061230000646452486702401257245500244416032234100342465442793421687401600391298362676188710658768274994372441259367636094487773123648531617602559568065367227794532090257944962104485718055709896717397002351283189981862859898364349264703653591434238200221450643549210752449539127970651460726883773193634755048051307048707905450873012142694318014241251440462852327323931155266740938117847401543316351965993962388118306575530391712899264849892295009998652485315904123329280420325147491142916467471330445485953583711181126438376369504196422382567177305118951919650997747232074615017191899060828187569219241223782010899796817031771154227533637664192038132825139974670065339422166527579955116252207577777769687419620435185296768631363225470074611871534082051126470625190838638276170326682801588196676862743727014793861840488260154986516356513069040506954126906616440755539852999450002529105287479116498894391880068241943465206615033135656108598930375043382085451914561696066140791120861267861543573243036476505232070832429756724459355739746545304761825445122536291368108493226959935873455929441812649619231873487640426596187885350775648117914174759237938010626154775008696070168756038444368286709352606171570554937450394573515970206549140112861862127629585612906966931732166653760849131308270250626590433505997371050109337888581056729248837604136996789184175445893152489573909988436841109214101414174741193799672959462058462082077354530579480897238518643622682090028743464540310721195729383320114972558991151996503142556372672059661711621652663096060540022872612024592311268537968691748583642245438885139480794463503918734347343101687197727463517593523535906310625126728084638506140630232615289576311195665066669037791111945806313685681381547323066384999309567985544027045465555767036050338940915237657970572577669657386906267414596135232114517083751436180785992102254987469622898489046808567136890898016375771407191827653256647537089361480185412133366735927508737726899510055802495482936033913535515879521892794274466422910298529089583757810478566177672751963685973807578437399487683761036983487025122592253844823539782355409204421151841413599932335430123121741380349205212320792373710999165794129809396739714451614783225034672150094878617903307147540333311254084571047725234886676446398577895092182944046683396363471503652935309972004918060803977032998963208416753753761551161072851067941274610965681425217001071009443960972138304262081914536899872453980013501545539972910077536328785892927265824523947303945700298000175192065951292848878895662466164885074404194584255893585018827499897645008766711290358335012956954529199574647788955238631729900739751835154651696882567571348671044062216887067743789295883476069504076851680338804061659334461444944370195833024442656615802851264229429796612921482151172185689882533152719771038261718440329605214091661563827446293102587466274186203255588370222452549491251453208035211134550759438310853617271907092332359471392679353631410511022213239576243947732390999512541772434972436288980413661273032903208721414074437727469005459466374617828349593347589103221248580522240903428420143799001529428333627084163012045373786431799402739762311026923641159707358072130382699752796508254620276441355981940973275262962636147258129134459561481152016814771489416911984796058438897569229233383829906026070079087357283722256655736710296671589811412852433840325215432631720981511161413822754975764739690259748556130114672703029263782767743735181376945047404678548782579800427496115139211960100766853988184903536883441589022247832935531710406439187543865559753931963691633870924911069814365126721064895393769373981234182265152879718698058092918847779096028369927381278293176604450827897968963146505138401670667552408294867212401997434281656283786148090708938796668264653459208254763769786119929333509337282845032422639252436070497301986742769649758598296279949360635173310653844306726669960178889417182147372129025369484958327047719121658887491169031912134111883415490444334445418812114859952909495167590765796578599842948339909276945993887620655734855974589278013643787338397046671482589012257047122177186955919109221549311742045403810276323581512729562352420594225986889240755455104626999301394381774103925605062708329329118185503748918484716779226139439750132070596084513125924940188155608847792346366462002741816148713807687777080223414009287000331234592572821779308972388125247716006027779726171409267113772289243113327817776354849077731496787519607329655180145064293436883144914425505347175722190552302513296105142356748531574497354825662814486517638090279030310201143485155134831499753421841135872207791158246644731627585879659055491370208417240678856901670625667660929461776117415997121795304165736942285225411623172009856791923147084418903727643983634038726529084050486524457986287494471044476780747159716310005192027306169689322331647887234101764749633005653677805065947476370472716350367927157353091463914652945371311024867590943269440888951263049203199301224145158373457537522296358611074306085144816335381052629993699644032718512051273235932857193085040057354397130864194087971518602733134010114380067992369277952316924394727601218102579978752754487063057385524508700759278309674149739944712309312065074073423475608927972943907109557155816378981950893679150652382582420227270482134487158150497606729883378702520280616276909363755514152892908771115344889120964415416534855709672169960372818389223160297536504464859238008497229710833930905689235359247161440240049519545337396842349141847860400881405319632941592681546454612761995251647309718894693583864451272983388569056526928491067298235857730136701559591741147517974136606167459351509236078122240966109129374046661606387030875231349714686475640292787107440017634082859522690288799741105354743030905842120617633114399017412204133105541063839546269995751003489869459816578324203040055395282402505696685467185891437378239052929169363310075966310627044972496816080135716354605865050022560139337215783471997927788224549947225201429387292857923230419032695471993729739290206348206659361796070717596796997632226837308256422628174115047987564264318405216935932928925859086942630602586444902019192812236134249655122694432887714903359987825322286878344299883940579881946174655521643726742128337840582770466016370901362765189239860563689723351059616997555270682541606824596843031941950445819288913622256174049084622052809757721681682429852029018976311743334230034436363886864858495583747586431564534124822322629626470503939591050027402997618861461787645010559194574109674725967056683746593998357609614749337940552436511801268226541580269250076268196347110968326618153479976374941682357272613716527061104521023503132831625655970673463285650254679609262500206113938629946747800399035298363485969226875931999608851504460126543877323080551953423576156248611397372531682659742819672304035857878776218100283037713675912996490535388724728465151056772913000997244246480572700960772298365220643327584579338137308654751456501710316345263499365464517636379068853594024724323611042466909408835011101025230927481217650934124160437456982644209773810909592401977796805539924701631955424562832769115349293089805715519542076729630898532680013667893724320753225441775694103872234490295897250712735515387128186986688003969650940610202677994417117365484948949966832108733011294273265106052689880125735456520805298569664537697218336790952059103361835448870947432905693547834856491701169286198187807123295023040672723259807686010522380009352754729365895772803869182113230629161880950210142146486977161903574390776039629926933807679943330230639684751316848465929559955361480862704611360554350991953081448204610861572540465497068779462207238821109617079529519628886538261058990179441070382870011619922931989944113338977940042837557647029747094461848477305203859680110516804061640488829135685869872456885316329818567563875863396836559337809306103612743455785488718084206840821766098157705308207540336257432458574791320837716132011407350988106046692735279544885912964966042628822109918500572381224520707618227674072158264780932025254697375816905660570372878797199421149761065797428218227623640357561380319206344924610492886457571766707144967004833922326778521468949100065993380803201240383268691808948941996126097682580710449703660591692823774553227441214814555769422216332428221757426213104276646991371524205456147592279859259072549580475181845518384951647066978066091470670638979417940901048568585798609988179547829978861592319250803507384487526448918247241823690691785686021561652006181256910294645501628098876303869923745540327089179414492499953363767356370929557592263921747686250228838802065210638614735935913512476016237573460638612972736698382536041103575853717746134890477328095141300563993019149331375572341936562684865359009386895076600327189702532020937916870435638964953481483291060581335013122233616662763281634357493456256746282749068931853906084812133476026089088438997262810369077884556812784124271311859685949245325819057157668158778306899771442242635855925006339910086175708949485881990962603471379991316591667820054611452648088503255296894935663333134124587192684871299817243490858640941391702920530983707268464045701683718596173818569669281876838317618994189585573499141946654443673426322482515462013556431281080144924701990274935191650345703525438863550621254438929380193340847343346926795322679275322820067535242444012815768757079863236429648680256993333342486911967612837366925151026036366781172472052695138913412834702888511746544351854961630926215267418527735369581895240480233684098836811957120645398528973520545548720542511281607307634769226775504408524593285033067233312939230970649427868311537852306972286155560772309805076366743371616045922515221141002604644742657712378700081103891219674942621469363250315407973415137074948893083069379177360196550839325503051656480059772467365087075973387388369979457253766361505572033388884743897789651985999124553809681255000558161176254396580930580501285009743211892592707583475052911717575900463404530276335821835574439119751340580061312336151291361018268947285022858718731177031215526703946060360082348886161553577775074304824391533181738576944434500115650292727561004597646227988401801526504717048835908756470072384680955786820241772057906737492684658229301264909750576109866203702575128502315588070360813913803016843354375951136919175761104920497900263335737105041073617095622394777462620888207303105323174282218455642726850373712399423384908623030268804904622914377004598685675051874896114444801941283649844531783935506396217015079753011624672054860040442848794555391668914314877686989327304049667631022641424201897537978436842207829758490558228198913133088035215800301054950268792995602287948341432007407932409947908217738550669038103041925278464076180102868085779253013946743818969995540644798665793222438624984771878174947773903948245488042234676845099390892848488094352098760752349364997619115660450810701257073560632230099416903831239872729506608895052138559314498291233088415835536181631670272583454543857269362271256171349603175177671391455514766410395192574134763728639150204233437506983056256298579469663636849363243238607606000585524869834777332996562668881856704551802287081676932555643181015408333992906780415364632862771511535846605215485871152455707860482632963319137369403332901413321349045418093499162155722886695349224702782417016758718143435798560382704748488909811416007071917085429326105688508050163230751587742604257672153421449007576128121361385381483009345086859117344624143075686784628456070138190770382489545682251067450500813872441641008120655201258678422351924535559628762972478285924608361359519395407281082818655086078086931776698700904984703649965262697404237691757171325130038860759833917597823030537835055507106911092909625241573920117832820899507142239590335610398935826651201158602951268776049251294638658934519177538482833384242466814779938318961821929097945247096964228064208710583536150494297633234946730793297434930435508943658752942177584751696301707940539334219884513680296533661246612909546006560247033881413590152140528259331716878812018776818449047153013645001877541716155132434240778912882493916011071720819786125669298636434153147393462544944135729265881431615061407505498715772009342411346729184057655384572965287670510427241571246283367721437123191795479052553598718686980256789673793377428017235521913343269771517836448371275861230763601720778558362371690274465261296938262598665756245528002482556843772474420296184829649302243149998281911321790960236027754336355587517603706004155291427714526661111648166635215800007666443852259575646711368769444174130610574869927481927983422276077068723871650971160138616496571947161111943701769583553209924334920591420896584469899066855424167461195690259169772482618331419836496085617608189513226747048398916793535162081415794572192039757140229841538167720686108451365567432630971894075556890637182101256938325060134333242676215938436735032348805549325805359859109320261991800139742999078946257999055210769042982031056244675659868821898787195355018108197989160234473907164571639776750851237500073375193621220924170096450283429826068162202097018293982940311223487310649497562602509426172619380603734409944735156708527846656597503628642940823957634850455700668015077117460401013139583452290239099797224268942536301549228478312063014368719382510744980791446594656574163587694278631800252997602821994491119061362316173881437678097393074982396668413996763144498691960264443053597052924467730930638842576766469005870499636116823054698474103405500769525697322921885815744629692085112709975844055971153165489198430284864061015719831920843496227491784929063100150644705070264238432992904435555960802368586706240475738451040040076884137860329395242189509655256221445993755801385556515910831921850107386267628644924410253412218287996485112971984784909140929629762787794765711436160622860682526155991048611872641318097790263092303459243717039172055261487017326324334754784607094324798637344308758198139486693658844712419196291281921961400694903503624857572442121228901044469276767383824782037888367413849110982351783006495260250427500079152969633085825865886680714982220318539264359055664185772915442040598948956568642459289869738327750990352157734006443363242417262178016733844451065239572828365189005125731306674979768704952563582742388231035784866740375678323196441754329962769771123309823839977157100650406165837089117267501764193487894704814598247433394763276544251446762618468630599732568795807699528497113606568847289915365478619246106258869389781066638490463289057038612559029099127550364302249226438805200488222123308843925811997380985208816597236717442559165802905446072217562824301597197139095018198995562267519738877063563393013763837894977511819743691348694366205145760740436725354187444282890401104238830715425897402077066514902529272313654063143724660195862017167543054541365610105674830230234889082767316470827496167501374551100215160512228049578928841930367550464503428055455419518837173207876142986444474038135218948985368292564315550326941604477123161205155573783041562988857682927126099779258426705460090128436000038214471830520988741722398532107212424454207907262116366814477771851088341447610865643683295353336084793025773155559245178285986853704445553149355113858554908304656814672939537011194827253478647260284129453161497570671662621153066364369958503419288787708512720608884618086949530428928992908787629646300943892823234828996327981911231228690079344604950829711106961896550296237586275362369714278678761240485641487446845188586123031559733189636292754821723063198799443503221611547728536127398719158702597353805218807170768596003854518934587385110688300042062399998469576466364404903447024053219076846485729962555186486475166111145853433589672273195445102486686031537053588682921236015466886695832719057528950711402902941968412944357828076846032452098076581279072510272168088914741578295472547263557336257261119471076685393901006973466245747866281201687796113175632013106025257000739269366398289193721390344057452335525507895493838549657105309370270341564321413963698815787886271718227310074846518299696357682330047859186418125495233792854115852180751933880027604781363515255409014883196606554142386460574535181419662144529685421576151268744425584245526044431734776549462447284403699855122042952905787971439344988925924286058433799634841100215788178099214212999074934337373917307563276062061718487410534910186485099223391877399412847940666160665549384823383691263350831867330362112376818106379241614598630094977056255847522846255877014583287987642178484221463138970407536972639083140626808778472151611197032541887233863096136272234768017849044842103709228980757670702262877459034310805151313997637552778906507555666558275281501833942906642721474781190083034871374492681511225202319452238199949337182630641117326242326839034967452774894925383677407318958641702088396284545454124522827037273469479712388989414177651817737344683428635077388281518765335852932826083250399007312950520800507654131098645019634468348436024476674558951845083333024447080315757149437972201301882630964882451920463837459443150731479270613043092418012244889433822896897559944148543283635416083361862321815787664010718612804136662026933933383054688003122847684048211278077113474348989492062047470775696215317518042896167599127294676275495430814609395218549028216038750842134649016632827859373285319633689598917660664510534593309909663116554433535677624394662511413374973943773944773305936783488804279298482420297153088095142377168766504535622104977307578590739683130237527570769227138863446848451734742150467053305496183629576398656305462137390496348076348415912784743692325264101874255099821390857882641395915504378798943675003540482953839681863063053382752685941395775764756692136848724326713359404293221798243456279275013211304448385030559636879308706071595167663697687748677273982044446432799683994977891385900961084574033145485502223066166761264444817001903762507860145159999544951350301617147153936198120346905005616615701626191843935524825535412763652255799484690665808573205658542468535234013925440071066757436650496060949776810514317967701018457995579885943816758686783056604386276525316401467090349514916331931227770422377418529314682817719348927283359958401997139169927952191353510752803190672003905076782427464450245968639941346191589301976433496945796964545607098008741829970347651032771941876294777556977912007487737208995699318407072147276477715033883714844738590228262249835234526856054387456089494646239895373781982839667936048033597046047427184809407024137500847279586612810290202621789699943740409391512827552329481153547000986685488790657295057303244823761574009760125891518771284575998930134515106081827698864380882099977695861044657375290382909664297461951700374098271261576088464099507408031775263122245556812535921172257295520894045105581446505639604812570756767361186763592153381339556914589391044976109836892922115712467282274575950081499617415502405159046742267299683661475181100613977717075583862529418533536529728082270980800765784274890097536542946696131266781459404155991104783173447795956530170677264509518044084400691158660967543529860065648614873009598951936371176783270780205323085468809048570591708770381093682141866657116986042992700451267665821403768509725979835236429469606566162502956432153822264407260720224486980082792557851640357662004921959673984854996398631903655589408871797511865840960140124317940361408606547947734972478885206423920064930412516261716023521042799300163471025976194498654013568346503275652331682501245363981015531176609226322107973876561306947116371057465190724826591546422335916913318417658236127360796489175735240966680419894733718810085296090135404954004574333945651669153485537209311122188622857144620899903030526185793007354835424432403854143133446557260773433319692219598647350157057193919816638669245722578951230521765263797385685485604232769530403792075246809403945313983699945700791545655562775921564252991946987015459231114776383377568011799850800912809896995076927665681471253033258398560615471916811470818977048898124408814941033669905165162400349296058675919961693213142837468511098935606568035177223881305165167502103301892717581946480204578884465417788288925093276049186242740663868465235697182001980565901053087727511768727667488479322910049174058837325610440165909020445617279041194701976727368093834897770396662356333746335691631017437796757555099269999898498206887344616794411890562226046382979199409582765819594689249184968522477749057239363791483817038579190724541883591666849115257458691719594786224391509858723536052191017476913977365493237476062272928094143069010907651958430945391617150547610779542639005380004071171343963213794105033479358922907649814673121482481844711757189374539774862564197488725576840354087176893800234259856877438651323951849094126825427938055054614263443533326451757911349796067369748302786655548948013975840060333784677625778790533736580404111394539742465920588456341396030331517843953744879930920450817525847493443158096758356393691971481990111568300853807396425844988255943580331614862603044739211849868638719749333153013114120993931975215622504141109410236306555101595121941808508588204973002467241440634691106974680547615992033582581995738429695879902699822962156597055060284626717115040681637049233875644463303324882468875054355731885522015487889001736689775527486947404891922048781312457765104904416262531584597674065618360599852786750705849872798154689677308150866884936407796213628087551188258013520931426209331572644890805359025607839856133177096984404640134196522654255729538677531425434691036202600585648249495628560323505948969838249337460162426522927286966871547349282505110052619346526505973779799706602269503686852923234491329089249469336076815536679529511659831027796580222276287942148924852460814738756691929190812988992806283195724405600260787426889352632257816821072124259341643916771398490170170716082543238541282084177398984481052151639821274794067674311278038949335452533319102544938253604575998633441232512061091065472910992425086459911602693716172865696601730037999994625700736194126891196405266413136178731783712872304478233542800736363352751181348647362258936130072773958922607129066390214399974214783357541716309179931586521231108265965822075915728626131969088971471646382424233335955005658012306107393751600093071249788650888024899709194630958174001053515581138092355033518856667662550839486390150711930012013791468791284163674281418234029432167051594802998752815109932121229538017442436510487050916983696693314017154950823999717434147182923589935509057483773683297030051345500594163960105113302882155842459264204412228052747609555077490195016411874980933370127880142186600893521975536078763563856890755755619031696925366047416057149928819104423729201465155345451361796058006812627012845617055792575672015091693149375503548558213116848792683525100373716948893969567124565364309604422478558941489699017289051646727862997385074995460829112065710033507088130218103671942768594240934021398253479016338156872100434122999528852235426947962653351895197594479944529101951058266435458847797046193345752054299103592895590643747638370649048179367201906056729785282298219931265100061855134491525561541102527438227397240456450011664581523766541869529105345895093827478405747596805372304032563889434871698886616874033536796370874272042327330171663123829432952686037743632827038524104020802983927101858851076674834299884051031592314273277759111757754566284530282458403635592195675843901645893586971684489731218672313437470848644612508363136081243205031976244733858339397144410366496932097530443140592967720759849156097661851250510839556361023666601991089093124585170353447419649266949894636515605942875989568874611773066363517736074107279193828782516333428233196191298331030202587673998218904327481270619066924621311820791853830647654783322583989076028602991537563912875695424090471394158159034966278923364428727660203746659484498200125593308534104850922860788693893145449230348804168977723465445826604563483566797935607986844553101029997832416225816848892262245170926108403718254263868256059364274781894049590853500074862643316207085096797773553196715085343092147785889147658436314919004078318392664926770550193194450881770092060494107720203277747086724339915655052156440968726256398586103404715945242138760051813717777249827783229938240172781351018991871173085324768000063877215683686352347268342168741024223925541680284281240186570559249051250729895341770009526850326397420675373017020236764139957062522991197944017049177106502240050650622726402368182670642824038163462328419432584083739965882258245316857073608612855260032101718486089045183200129715092256600686770824073505257009846914629586633546159885704236629273531170247704857591788789177558626520819880198306648225644067132811285587631308406029851035899823366902510813574399463983395677883405484613169028489621146482989621402987971404046858565656354938084743023033249304810320951639818540413519281995098901878938682001051682651849775944938670782016612639378085625273590750833987649340317160010853067184825650411322401883850426954618854559582620803119579690325591519719084934300943483294567758689037906800827398383893707510103618511826933066410080174381563829642288114569318123788548268425009447327907914288122623152649329550237364040842996921866312023284900197044691723357743556039020054713149003275085147218595528893929750763121337789983503875301817662394224666227849721941043870886347821903320087465659133618845406928276729102095225751530855605813320390699887008037010898875130431554783433625032291045191631205847526041111394357759276987944949057199060005599089898995097841647469523911422289329048280214500504749826889949835418897961604681438491842420266894827034540480544806014283378984042957897303234016178981521155330791823129739852770998622310544060785358065918014076875303868882487428754654495937453214995385526574607713351472524397282929809667417164279701793373330435890307543467571110956269841345447558121196543605475705513065122124847904241007703961223576093194118764028483643639610856839334395928039151023358224736059619766481845176604559475073182717433503109247487634405193869419679737223491247488596323882774398865720097619453228370754800815836120919690922787118582493469410142098364307176945557887348142330437742301418610738078495418120789813849785505847078424401259502180385094362463591165822935532722719526133500881028709310659599691185092829216377281723220010417219600270139720133974324131366305154854421767268649700996175775935012426717879319709180173675360259402129617108282170296551483154856499928976647318596804373955066515436994945595592843341461170535431920773518948107272773461595137334396785225440098915102760722782791912553875219216780389635616412744737604267446132013051585700269276644765020061437029417743713890402965127307224568248174468262083071196142803009072342507392435231181858476827836161928285587120697412191026982260487853230506141545413566751047740958494440956988035137306384807304322949794135066996098753790270534379531444758073731285133681247144069561670816861910806413434599355315678951696581023526043719384301543985016440996868498510443708357654755531645274243470719742187796171388126700384906585282260669056762805185203564909193651423254924955112901432574040883772303150543641114183143254571021439634733646986597004298855073400480800362065129489519889205756395414313112990104317617426913560709590883813713595469573897843387611959264588488348811335700525101262287530986391822690133767032928758776909136929045450278617366190410605812062512731747719824356656478299568682554662925786655769409874644240694073827239600153171983181561360048839948866194464281557149111662288018310347955980917026185757558198259924014250034541038210484510703552967812077424308777739104431978222499665279407461871517593983811880470361079342176540455535008145836948713376064316723300191266631474708225953268942505791335762330109937507063028649795429055478382050346290234868777455589777251657773409447008178795410835498979159127372654913609268377776508220120215675477316643009537254825057202840253541938746885603558949854402625530517864609361017088817142576381362747331973966887726024545222746467382168173950981449740274135716831021305488801780412081953188975852173574068094441483705473122360796972020720708596192782618125090456664150390473841432585213411755328040712987942485359044840770944436977829750953106552112136211452064624137170267299776804107784731098778564463073683398210442458892751508767482737658313535132924293492827174400043141076837635446100178456311433461051065477899679714655871110679416179816149835517397799404713117488567748568721080931810499486943940711728154290299987720868566690758972160735289150290617469017834768932226496130733648528867297088444630016759404223871567564408987953283107935800593191546528062819772770653789642581618595731030911061492316014651522139067183533484584039359154394523684469876665584032655105522459040939265220949178241911143229650712857445578249492406218666844125869120182613893968297189454045512655859567482194272482738669150886732662286614332992860746916649913768831379469197815765785930850560097119193180852967241675613646019310494840437261242479975284897003567238742831009747475690906330463172430740238253181059735389478907727140732904141238450040985357396214305881548619129933551806158058322283872742095740569310809395001257127272862858608563285832230785396837344953601950848092576061730248096041152078916418662228799203686990214927900844284441902124982412055060275717261990444130788270288996112934846038641966199851577742253465110739822501520796053758018090646805707991913456379830365931672631402308776616387738905602671838094041011624913301908545461226606047594528227127504805475027266837449525749087563880497245267022925149534988334121522556923479506477187111122238169719976295093210560785232124464518532222038589596091752318429527537721532846311688447324787981293301930056953207453665713843467268822138321719782779305857835235865841628609348337697170910542898213559792389290816806090055519949273179083581566283008566022345203057927214353524169631719658194472063245459902743328846163032612476575324555212287605679612431456727793958963009129192673143091915556773936235104708341981542393728950274648472130761733525735187533125433466883582529831460285764030796290925461730822912961323663555808406414803292826555783545009283690921454472878174863632590829878849787565527289857271807050195333911902641674333281998250962074808740827704076634286827303831774382272593741416344256864261589597971192173146422289644953807368173390900401676781934345281734109374075544197475906056229945190053893638724514406209970907603143994160398927691799513458335054254729192521425959527294874137814849281084065030649463375406044669478814744343646383484249687606297397545210424745521643751083223925582394916975085656467184804235810241471515867226083046136718843712962437045864168507838273880380962592638396106263588578655096260491639146050214919759742965484895961921853622749467125034027203857742718774609340568081918303056729680402395058190697326718442460749938353925176933760542955405057545172752889640297623263375455773319040778897046163437823932018693872169024989033952409478214404042265850392597207279756283911342134520585600642495697766762473475347207171247230388111014753153498317338360840849017321259345877618914064308628844456238081209470572517275418369223123978421336794525706091297949879638114093784777675341010444858493000627770872184350344401177384941372567138586401758640087295577385675460088548152355943081403665621596703297267343090406043122497898559782215568241967457160443876387460455950015427116262215504268043462549823390226294805870387422910102436770792118167697956546422654301840097387000344641183187799163622218959727194265861022689717833523313045082127660528023971238414228641427818423855366258103208499592015782925163029571184959240287793068818238825592398193886957952725387768161886888120351809595201446900948468971235029713560167737648472559490235531814832522646292327516173137766409927707687295191008034971249042293744596848730598534996775939251647828613651393956703289456602267241590821929036785542566439640908249035242396044272701960143119788759452217701036222416016198149046653926616249073738278428708302418336075788610055485485601340567854020641980259308662227924485279068017567719649896166205982665245447255813732146850122273333416581280861276354864641874392909106408190390186363740162764733499142926416829189218418541707233867427986401155753709778124341839629235676461619320751973894349853154443037376979814851836233858892401602922558817919277672006698009530791823211453369959679700585110946805616269060228132821081175528464794494121814135699425347810789712116040408544048136547567205187225252473339667732309439683141190247420571459095914994752617531542925938884675897518684448859623725118319171220590945181861696164314152977961726101779935271209596450606730179765854102661707081893888636688731877088857927842399072735684597665798523354619966050696004264044237672366585265304049809368910389326631731470293295057970193126772774185421640202972925269515990811913741109428778207915116768077613679221222561107463366774358739135893193109531032087162781472021485711729894644689157773293631060040405643275376001420295237775563495007310528182027920740055329613576874317836903100377407915347881199491578110513164523673263167580683413074386804076490770938172357535547288016168845605584541659510325783429531086823810410406208945981383337650278633386750354233408583477699712143735870172148147985601820791153118599688148214683138714963117716757862211702726527938169842757977638344186870982998865775350779965360985424348653281375307385583307520983866398115877856302900599259887958219283927317580561306958399214083302753337394855942665193089959973405415717904236892286540562364140619970290891913960887126683505028549288822543035449103835377822093191085534177780837148313528865950818371090807490260735322759924746619939609004989583788338807613884499180635115232696849686914552452254921997888167613566064683311289752408481198756597533787078826018401303868999643030814017689974407855156799680485952620660670898579069011955464763899182617236646685332314506911391902360750318462297047704374634923155920557424303045317175354749456324160720357755430769610448699330630148032790560953472093445683990830616543455611489828807229282907671564531416555856844626637117640540072216024256477096326598325173088815598255098641897550996202230435230109488443586274727093807833253131193850975824563443227107627843936296403379149857399063701825487084664083658611094219504480348385096775217809551795970585600266931995264826927641646307606046228604411736843382337855645961773159066247531671434196352318599486284598642556253574186828591531442786575188365746800316215072521867917124665072176699839211531414114467209740595168718508945386216151149949123910809142423815625564484474664503868346837741894931261861366430993342565581888469525666062075233182708693724896775428020726477867705761098021204312293438921192869646742834868316818725425201753223108491555219596265863193022039438635696452281351225096442972086774359116519744699885968359848270957922281118641223079793989806021885562466130526476577212477990873357687859980033210455835763866819729047624280496518251593452432137811685787022468885099631685135465898840990364875632786292096783453758483609641301567116147065017233212409038235496594366788264726994449437968507837553406049807177366779132771874922350892529786311540403113625652501065890721564756421241505713910400182383678386795740769136395983460148852331438998633740875432697346797834474548958713704906485179241878796329941079567418408373668837665316345070601891400317467799846826157981876946127187038799382775196617647539457687613605695245409355267990555430394351652008639289297034972328269148828060558869193722471421811871429298837436474337839458780764226333051525910073103013263228512224652261374411438473019259851305153550811915809202313227952424770552649867240604917654415619682475953512175197969301546348013753523805430428925328565427245231440184374432034744301973826786310329121479738896853544821768755199518956519206004485375662704291125654154790990036948795829901543087538106720208153361675164188876504309475553718240675587608307448666230897498279766721948945818881470754067628805329296298772431110493446601436678779961947275753084861572873577142669534320836634626976811115092820699585426427607384446965726957754834679148517266652193412056577425206523397011051096565543540594971637555799056647945611693123550414635937963104526226044117155046930029355263898662507268907162566087852635443160079735707956626012592011663581273322015920869923523348354697556816406723785103978321849882505826407415850804484853934236239772764797030607070328844208826825763601940081615071200937658075984850281197503239048829075478376178209860005492847884535155529040523667048653894578815361387518416015754241745471133995856596553066420143695420878352124196126348505266243715928628767471129498174602153541058848287439035392990312335447772711831454301320461950279887171619792173828774458029710314110528553536881032080159407094863457226479860626383640131240799945899903711940760333176249534865561739732341542461723486734462991021920664459965312347941262638920978476719339705753392075431049662590403460464136508966019525537667088505296524284709282435316305656315350994318443675989200979517533739619061884040628907973435105944830789487595717323490037585313459999248831336479738908896223618079172766529329081784415416676923325832412410875972815157145576251751245998598639682417553127718068583310414318453814061753874423925620701052545328355378643314528515239107972120519119134247830820829843632694245799499767083144564249935365511202563090109645062982086473279464946788734076941909130659657157509771599683602192952327334699319389182132327282308079362954558653058880540139847045223763738747667337905243667580389189069091839022577861826361201485006852746755478157230302865391818682074254323453060432517475388628583867674440267581540182051375899608965108594232602339440705738593975439873312216490684305465509159349748637510127845682026617565153371537261081533623612654545507668378103896421780699565896526777340860548070568656465561973459069702637433596081917481724121619494740762342994324207108141842046483531015994002304673536971671983555209501164291744657962821165890614790843961557106763095173984224025467133841002637648448350184133836498841894864632431074667877519899050741053747425652616939427733084506490260011377528100513240015574825867373246975651670929095396635909230352030660720371017596815890855565554028397241755493479847642955591133917114756158616754514491599247043772550456915819104032370088062480196223181218715566463284658686061326322200171450574943649945671466213763378870341106705307072621862662083616573250735206998917410937377245964372173810822893651060211691343963183998881178363858001816194352930404585236432262121002508349835625590289736315592210027198820271820921684472532079443721597163076702447580460810739573048983825850879489218211214257777028723230660660256564554873756763183625480926515260470672430938811734045674420696112098610326826724322172278555199292706411063183702761853852816443808352120714008753916318731762995598063974603932242696854655855533699766486154273486198619760031102279209466559216170833870538566871700855970497074040586868333443130377902251915848140585777476269148083894941267162287903343762422136923968438389718154920479608098461723405182991622899658170325757000875760186975407817814735666463436065420615313880524954801019656790958754008402982485700744720854936073700392858512372835583918684999253134115764180868450160090778875422392822590023636575085435455595102994305030931979796244377368438785846082895757012658282075059169445868789848164618859306910247076181715992029934467621209487152354143561961313070484310381069975221119554336833079329446803359506142032827081341028562692590750699406411011068014888640498344769237941341450595485866034731911555891954472102810138901447456648148296177226727748181817744799016366973400803327000110735189301665818388047406584206377809802913909457098396238819115836984794981420840411779143190476078342162784746136514002588673466229841102915629616048855792666084686978729123757116755830134857417879900489780562244965205091691297426698230007805175299364300579119072937055809523877914973354944365327399271086540833856532863171246257175044153959288317280555544132108568773758493328659247116334036917062747249776712464511974309032561463230171859027218039769345213636064277024783855546198117050885856510149757027043594742112516872485472095133303262099872876359748359267646037392958756433356941184100165206728735724777819978530183703628228497296899753032917537746686153887616587131001738227215689262488077615369219143648918756612863053819151671216531238390176043313619053720740559811735683819175853339705370678306163121539412656046118063696022464448552890624847076492115474048809626439167369472731204263278998162505719277752235237335831939398171831562026741682910121792764355812429954179896213162953247684167523942504608028326985153510229947577360611623008309056216666324867542078424792006395257583950025265430698138666880443216520049772276779382861369032120038639977363808801925446123276871813905808643253237315562642327029184541497805573108545120012031493443892041997772002834515595953566546016307366799331996449845875483744317666211873221836632309349905577301877191292896248916658188781653353833761938090740059122815449368861522262285009744767680084450678705824387911600961928715902406051647467718563808214770731369334188058680385843333948348250044423217368471552650219548309371235585691276608875801975521539299401096466192151477676414957125012275159228741496790384978309349811040496483551654647108897473438792413239906145830932691440329382325664099173750015914867460122172430412046661638153085546033460946033171565183772190145459128836329373914036324730272221585642143463036038204145858168679800497282754012248770160016917027896513091102959156254180752375556464311165446003311157237167464558500136170399555332888038495224345295651155362334088365525675909375117844823081101905864788295422400202940382078913165495255683082101176614200252735787064897053673292821659905686134049878597185201688005949231634545732109909488387753905956094307292743683062663953770536880754963275470057727477431523966513816421797248218586069288034274122844034884424105399567678879296297504083055986043784042553415514442833780473328307997239395654495563991722073378388248843153881093795705760118748940921513747812874176951777050642091231154494172601667124188594562533391353636453622609399612184094159610041836966522695420672586758929142935084498011695063223544938283182096245443948215387831483295871172593892244201681788043686666311126824123484177637421291563022302619896522639451840275549067090216590500502837970170756393220360377919190735562542904717741978912905169121006382877303773022478954404184365234396780774805560490596393320313155391668716854720868147003152969590376226365000482134832254811921678621267925879495993703518520017282702688108492134576103447955907634863420407320340011326906774588102163044269663355782729729715994745517042984481641644363399549269990280504605573064277239993738153442213717167338816467232626005427564876067752878071035841024178543412333357955228411983973715131559600217122847663452172465309727638637198863420950778088657444143982691970984269250913222444139016191569732148792961705980396493828709443438506893228935208033624448703214154364256262431451897534236504691950677978083301944115207031977026224221420383948139012965678155128721396435427923819835832368966077935429828605714214804480034206028201515649027258475657826450507685067585177574363363255486787408974834995006323906616242797452516516459501023932727253817106133019958682780244191519283473344197693609055260755610318100690752903469215417658823963508389775117969086766238616321734444792001912694176551665357474431351215631974849371222389838384044745190061854985416715987897248724165014039505821458416809980128286884203739865690671894773380653378398742827745711519847774851283218878076000362147172154781368923274452697788304316186216380951607456062801451874041069507329239801415538959687957610947593341844593399978135688586560721228838458143394264155508819033145951720721636812414470764483975617347617360497117161647043899771223763808168967997618969016547545827744731936160619531515317136317438456172538514110231337407147419954366634502183252617923572578723438652640452447381447748505524173096770960568036260471970239583437229978546688868063579191615978214598294997292538536912267237223262848231075268826572634624207958790326562391261745765107272229560226993146209909280252512026373584097330636719083474369356279258127236411410013397593661051961026280189327149003856881458008443624952062851916676948479910500703259147009841425110633025134087173785808806283732418278078016889262532427008347735047075922378297212615913562003467696834507180820588689742219821194116676164650705168063714134029950376445319128131143796889398951474358289550364504684396154042512146491817546017745723933170265497423327216124307214422550552262843596547063471293707048661399017371849821397850665721103372382718365067653097994342426559517970416005421082344846561322265746550862835880311761473256291910968944101796545990831055739805828973688262588244275625371053215178625520591987471235696244766896283679949276788267492156169051033559451143366088006644813551253502575136211035893846743257266643210995337914297336326024107842818220341390925504819583348937232910020177215205878476827649176365350317153099864233377729849965935024393850786227533990510171143831999061377171213037329794880302400545342571385106061455495795170926663405132882164664419167371522149016912707624237955488767341854442668846176262409722110757939022189028865967699717146723077047284948868797322301006161227868799986791873935825900167909805744907075507912820223062368514286288250835238244207360468402741035702206744860531360373497310571119889646723481852706504118424309393180219459681521559760748133993703265822128658258620078113159577868681858976938322339672379133578900292437753782994274392708335155225328564873670712273008554384469386939688106429090034805060919470212308243394338608748989699856084298892504239108893578799642204510707827696132489779467290527128434627558422030508613833792009002618991017622017814355592759535235493663960221064905627472152898274674090315779955704777921287067753990576996323697235287480300463895734894303712959840500978130054441428268444149055725662336369057588125360669359925821709913255874920754920580524212310194142422342761568845865118887013001758674585389915903663476429660628258958417982777602721910092705637118708532499040324940529308409414334970006448404103480043571179253091296155702213686754603736205760359861400761677607350208922706314571174249750803063664472184072423523537444278001990539552633553596448597734031010968286563382836585335653104258641605061348333022761717687537106564749027691765979836673037867807510590847466532769592328986231966061034087511634756791210950791230824335997635725664319778970239780217551861614619440272074098885357800841357138976296598507721516783203199911178943128028613030929998377741700762936454204326076299060629198494474423942988743869697326695387763774538393870956568192782050093446652705051370856171226596300765410388043585724865335968005730210831731447453607060903829591660652454589856317853652241594486660125035437397326885292833789924990606521291396631526556457513802075039208684261142332808587424094309053124598721376593982804692693707031745281235027848571487841308429093954051106516514034667767052532216153192251577792273862340108054731272606791581549646609656491288173057263645081166359216422782107641458014401869265480533351265620687018815840015492163171539223034880484473478029559000525349235861395610091905354293396820582889019398333853716786032769730696025197197422072642629861786844408548785789687462339477091409885355370322489513867480227258243139695348829912248539485059286633849826358524888541128107894007564624113291805042268869388065471457381155561642711280937676929218633101373093424698215891419926039504243638800473246333200485254769370421961990977131570010867460591277586201895233610929752838957328501082729030269647612320719662743713337441880625298255087990820764417601079330132443099947688419508053904698773101370679860554817843984719148811344999650555308540809958607364748907069878964564721027069832897327779427147800404208121663831079486804952826431944303173409428982713167493494467624283930767630604638796947481252359203807814061230449646822658439926448704338763827474552238777825467634627746400515559380489587358898091229441352985562405411936906067287695321971305538418672395588939241249682101761516728748190180153574098860066094783502073465301103975402450617235923094702256850124484554229813122228283157039424793119005355938462436066702172010380436956938481178380653011639194941103048758498809973438435503569170734087230050700606285746454587251621162354943537983363791375463826987251861461974585275784671593310762572808214324903237788153158497910255965750816370341116989227467865887684046684902224342090343262909435230881965718962648223124660467357559240812827070479010900408290987872872753208015296228029597986078526454698489108439009507005544121483079278222804810918713209893649489674290805541943091749638464824304623789980301045975251283396614721750172243412792319221190755787443151949511485535276072864396129816289925850745423423309134552270151122729517204915603779373066020059018823071910454227045401509081374519534563488059698514969246020860954797385569438186426899900381820546298048007423593813018211032304225035568871267326453462161866927018005367855761326505315753769119047971369731007817685356210744133465750555562363656886663663413213994657620702776085686543022033344285425497006918249498470410178804086606257997402220033550393311722771656711642935238985424244809675817625066661169285110273882517421984630342032477173025130636464076233295547664950555363037181220898610388517666393294282559960269329999686198741018860988253502335078897023421545447260575318292504241214240517748893089393827153502627670642787488077254081401901110850148902758872507695929626594017122045016500926656975238781935208287245111306048537104981568406492918639600192268742954595136012076865320091942345308511293030474718675855228070111153673760043510882320107555607452931002300279840210993043920575885171740474295374699336577136813246292709911463558618270001817660325972781282502030815646585407476478608411407310493669132522861233647722605979229508640593609952228290021277890019790780138747199411606902947162809419521902676949704941922018486568085873661640178250244262763293519290676162461049930898012235215772948646068219882081997514657147126719321972179467528596865695966519791336677257771381840809149411516712268501968469703414413075091317642066970649430673869986427443643184922834690159348707229378866276851438943004365863276689993897802157580893236994577667973275785151062404031733169719683617789911462673464266703205030994173555966912816745496557109318482908918209002908071660714404953964812000798711554815195639113933400129895664069765349161393055961361289807628256139924974542475677904280482362244784682743822174207931669573468740056826904358255547186661154376009363960951811251974007310059046914291256095365817310694898069635492236218360403834331585378421748712060681591766908988776329177244050694546793106625100131933857999851444658780700734196404886991934169702556926659990700202712307334091611855282155141465438169576119458839035026998670006477802404362383814349632379047502124366550708022460550588036904964262572698388467446668686116075384802476338482911712793300596840349953206930614837061462642509735306520448810224366808236468440521943935285854533736606135267468638025823274205653556989977428544538912465960313318709744931945711262728626039083869103249409472417856693588205145740786913545429953612116643614328613783379796325678051406647136938749407605946359543587910553358315333109750234622102382870193479449146286764530666387697621886309007764496520994777165625936128858800360863417531824812894414682453548562071387424817230260048394223003505221058120189390142151071332412179654873225515529463450526111172286927245643494962092295054259988984740069142344601013079197578602717244704402286282855326395582844298083237024548516870327614029884916397306587234462126100111028092351639312279339849459477808270975324490221450188073746237469085513065444794374560523664545524272724879684063365092078556877990464330488884918714429819449191831543704825267982068611144038771864053169190903589217176195081558351039147116421049075928558253733542729609329680424081071285211841072890708562511143241746935475998780091875646195652055375292726698193315249264209593735698618661673403427219348654287649609396844918282092215485913769294415501644079876358598234643405509430955654990410656625116249617738041977652757179746715973225607814880516412264676264140324999125595634165798658813360690013672766953452793456686550889246203671147221396809369625277157344958035048951547398160115520230080641843990015065045377536772803490011795279107827247960939910556005968641927318676570241684977951154365562964569501602439483365914687615228511883409987199705953685549379904189929789463692411665055863159824713507916071085358104458352544617194786815490510201242969872735165339935031627503491218274418054843629006398359276278277154529897646091721371924406621470064670869360742479788269619337331195766416565971772236321391875554368152586464554044156006551969515284306597066038876407301867380002960498690364383990167202830475194150442109739529620327543576853677500179543944476164590141959343722704074554073871898834424057958670633802193421339509442538337104628710417567999702025037351365690915961241333666481421905486085545538034690969821578478733218391621021423080016756041807549364383254560669329170088168603992017261027976746490281564524713794699776748949030627252804759771252047936420079435530618639082752279443150987472659032230001169027369623180924764322237125836371611285936093087820771385087784450184354609735957968068686679419302049559668749907491482498842859902586166555246574807434426664559806185695629966791632158472422162361553246702030464895813328221442030128729391866706645989853487538589374547196988118136984096975689396263970460433702250734674594140125741657799513942485442470984120900298444046555333291000493754744970747989788839454069335687766129263374938587575721682555545918796796707466354404931966558198819812121727942853554911515577803520688167820676226899754483729169973180941313477645546602460355940391867075106433123332074590911269318804876218051911139477473011921857439124028711013424093612492944426525467632103505417995060434666640928290034316030914601924496993126955017367472080104416058856341056964614491921958589726903815080562539451086913380163062555016979117658870264250105103735108505987970807560368045839623165518341292585596127463060254162583975246320080209300485333359326615800511773206905293870234400072951581416583260392863840735934207728678049747336163123072055094669342331141526612764728129519862971025150733846593472541434897580923582513844216839609236268923318422438939975139824815360967076651518732525023883178213205814947211505506033471416401971654362102155418119459326405687067073682838842767451055807983430329971147898505182091939146413746210449991252208271401473341218134554426386104269813789207896111391100447516203064308078814450509000211630876491908337799854387033475094344006206435175845480348165227952522972202493861291829619470628668120651801667952022793765345493394355729366472992095460942159767735298175861417439643869966446860218411580474635152634355770612528210367835798896003464128796081245718944700288965447313393020561606896891932276178567146950223559855498320645505540575178589812483212752066270042854683654470305721409246700469421543251056690423748459861637691593915926573704073844070440700403018814363867633838628837212997422961660972959538509797585825962758806704538640224147121378480162752837144897379989124425218456419736819072442940848203074251321630658460003654588165839492622855087665333738590783345684481349064966699954056704288637406603533642111133649860221578156026459275477536549259079102731714295736362703722612248543387111253383393062041951846489336654732785133382417381573023345880010135626826112842202969698111487639336117116866517810200234826062881652239223420379172211342563539988319122537131253362478381964971235126557344145074006348244952568462379375837784140131432943213575458818040101811734701001953327881890752930322725831691555845685728244536616159430470747995173601122044381658790316227493715673296233581212563458305387605817635357425897232103711112415001300170763522433070076433058185675499598576138465683184281107570800753804219789862767517612326466468067345981861607682248856394528185810640003758182652332226489740994520129137849934940390281519458352857684168365333552196882705401093830725269340160746354265767318924764229994642897957601271369108819137095423571417908754124890701009622503821490026952855152159698618993931391614487509110655326365793116927578412043721346202032256728436894850641652612661109765414307748711731206639553811056281599856469348230180874958254958686767272877643419965852797894992296058429957034676866847437360281437936664444420132477485817010919865634125251550738422073551462156246149301428408432277627019343203646288186987681448397642421169406983314724156230232289374629213966117065548980974952939834799531737633552142911604250741411831709462899241473890542369485871707657710334192941797193069873436940937564594006527160920630929331261580794548688158995662146119910127045537765785884424247739251560647902936029533291782958162859141945167338627801779883723742167993751022373816165634262964721261668417586919028047598802569494928565948879956578264958080732762110268526036028205497277435472119015644437070793016284041607528970080059861555696118389055290194192551529128198329646712718597722025261847287390462042408474600696158835798263540352237068581387322925561398936367975315388132915084675242187854861469019517231506167221285253786234000072268568660016852416095664267390648424222680867911726098109342281055132351247467890148303701027292913959151550398233675511206708236183586982894918444694200931545628171534577440267439642663245623182094847230891453563527155322109072544696782856998098493692132428702251118207481360437826941050229456994501336051979064675241971732460518560604904510085377737767072834436107853745927366653020496852773524626988091443241917895314543379822403852156563215503178567745565297735455208981621729492132934523913362923447653201986781381299732889006299477172561320202513116930665168597594100583747753459522341084039730539768919191246869058728003746161970765712996863469788907157346523730694757074928916645019026164284750112462097914696105646498194828786430639656747129067488528624770870699054865435092390701757316088578556806397324772329379671970687701586902352966164515245818711647689829856857783473577295246485541114792096809470623162641808525249347357378158655612466786198588921298042553022229041919964023424593864908018003102666996647830808021421106316702039310807315780612740064944951314029010696480724996229679164089133487405560445145410844194276251899724866678280931470766726880480599690404828147902410089744533800659623229295645299105162328067384449981242873976971845407277511793661798656336667855496301200942552907573014493140692015530317013725407913163952757214554174189137558558784952119007239700121241511663305857758475384507530201290838495013954798003299012171050843547117009568101602967179305177548270090056863659164491534176137285167745283505616060756698632571027568092634259389849057174497598323550714849379030509325229548824353778815800000446988083787156553578291040726376890901992516538530513412075572855656462814567522112613310804914327247873791362793716304774265470721842991993176324817891801486554714795526558702279369064291263873976282355279888867390956279244663705924071966962988300720889203372557253479430816391242606238098055943498783373198670518675877501601698263835769142159600974088964085460141468555782432941594344617638296935805289910464496464185878458108130394024190834064808615028138519581669965228877312246434299973982624446083963623990279925968972764474675744973741108782639759218708792019471789780974953722328196076360657979002370890513121292148132076363478419454972494028140556293825168854016794780269200165318814059533717480699547805250874825216216632301052882829167952681741244830234236380165001169437202771835830497032808580209490412998964047854008651448131479560592370584740600384150847821851249175152423147229118935451471741358487557589412279744602275830632412093795554855339597219070772180114135902000294383984624205397739077427715464694621765224365310072923292664964722902017910148864027328143565586546955292463509185331760020058204859791789116910997743464582792071422768559025159093255972424372194319419932005710886800647155664681298537586118954965542315232308923742830058096318937235048832530456399639813828080522429624933852812921318507065189126767372811422805744664229815764886439915587654954256681501331056050006007219239206114181707388811080335125824069513985004021577790510162322818806746688789438464673873841077927269422212830491000197191142245603480670325210835291060339140450742198361798793600629098992256195971884980911666554927302043314617285744441751515121220211027553671140856502987839986462095983647729729495886849224507978157066640808365167]

/-- **An odd solution of Znám's problem**: 24 distinct odd integers > 1, each a proper divisor of the product of
the others plus 1. -/
theorem odd_znam_solution :
    ∃ S : Finset ℕ, S.card = 24 ∧ (∀ x ∈ S, Odd x ∧ 1 < x) ∧
      ∀ x ∈ S, x ∣ (∏ y ∈ S.erase x, y) + 1 ∧ x ≠ (∏ y ∈ S.erase x, y) + 1 := by
  refine ⟨sol.toFinset, ?_, ?_, ?_⟩
  · decide +kernel
  · intro x hx
    have h : ∀ x ∈ sol, x % 2 = 1 ∧ 1 < x := by decide +kernel
    obtain ⟨h1, h2⟩ := h x (List.mem_toFinset.mp hx)
    exact ⟨Nat.odd_iff.mpr h1, h2⟩
  · have h : ∀ x ∈ sol.toFinset, ((∏ y ∈ sol.toFinset.erase x, y) + 1) % x = 0 ∧
        x ≠ (∏ y ∈ sol.toFinset.erase x, y) + 1 := by decide +kernel
    intro x hx
    exact ⟨Nat.dvd_of_mod_eq_zero (h x hx).1, (h x hx).2⟩

end ZnamOdd


-- ===== The Challenge theorems =====
namespace UnitFractions

theorem erdos307_coprime_one_notMem :
    ∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 ∉ P ∪ Q ∧ 1 < P.card ∧ 1 < Q.card ∧
      (P : Set ℕ).Pairwise Nat.Coprime ∧ (Q : Set ℕ).Pairwise Nat.Coprime ∧
      1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) :=
  Erdos307.coprime_one_notMem_solved

theorem odd_znam :
    ∃ S : Finset ℕ, 1 < S.card ∧ (∀ x ∈ S, Odd x ∧ 1 < x) ∧
      ∀ x ∈ S, x ∣ (∏ y ∈ S.erase x, y) + 1 ∧ x ≠ (∏ y ∈ S.erase x, y) + 1 := by
  obtain ⟨S, hc, ho, hd⟩ := ZnamOdd.odd_znam_solution
  exact ⟨S, by omega, ho, hd⟩

end UnitFractions

end
