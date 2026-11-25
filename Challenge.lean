module

public import Mathlib

/-!
# Two unit-fraction existence statements

1. **Erdős Problem #307, coprime variant with `1 ∉ P ∪ Q`.** There are finite sets `P`, `Q` of naturals,
   each pairwise coprime, with `1 ∉ P ∪ Q`, `#P, #Q > 1`, and `(∑_{p ∈ P} 1/p)(∑_{q ∈ Q} 1/q) = 1`.
   This is the statement `erdos_307.variants.coprime_one_notMem` of google-deepmind/formal-conjectures
   (`FormalConjectures/ErdosProblems/307.lean`), listed there as research open with "no examples known".
   The hypotheses below copy that statement field for field.

2. **An odd solution of Znám's problem.** There is a set `S` of at least two odd integers `> 1` such
   that each `x ∈ S` is a proper divisor of `(∏_{y ∈ S, y ≠ x} y) + 1`: it divides it and is not equal
   to it. Brenton–Hill (1988) asked whether such an all-odd solution exists.
-/

public section

namespace UnitFractions

theorem erdos307_coprime_one_notMem :
    ∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 ∉ P ∪ Q ∧ 1 < P.card ∧ 1 < Q.card ∧
      (P : Set ℕ).Pairwise Nat.Coprime ∧ (Q : Set ℕ).Pairwise Nat.Coprime ∧
      1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) := by
  sorry

theorem odd_znam :
    ∃ S : Finset ℕ, 1 < S.card ∧ (∀ x ∈ S, Odd x ∧ 1 < x) ∧
      ∀ x ∈ S, x ∣ (∏ y ∈ S.erase x, y) + 1 ∧ x ≠ (∏ y ∈ S.erase x, y) + 1 := by
  sorry

end UnitFractions

end
