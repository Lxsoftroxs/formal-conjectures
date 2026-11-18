/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.OEIS.«108864»

/-!
# A disproof of the A108864 conjecture

`815634435 = 3 * 5 * 7 * 11 * 547 * 1291` satisfies `σ(n) = 2n - 6`; the greedy
procedure subtracts all its proper divisors and leaves `6`. So it is an odd
member of A108864 beyond `1155 = a 58`.
-/

open OeisA108864
open scoped Pointwise

/-- A fold that leaves its accumulator unchanged on elements failing `p` may
be computed on `l.filter p` instead. -/
theorem foldl_eq_foldl_filter {α β : Type*} (f : β → α → β) (p : α → Bool)
    (hf : ∀ b a, p a = false → f b a = b) (l : List α) (b : β) :
    l.foldl f b = (l.filter p).foldl f b := by
  induction l generalizing b with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : p x
    · simp [hx, ih]
    · simp [hx, hf b x (by simpa using hx), ih]

/-- The divisors of `815634435`, in increasing order. -/
def divs : List ℕ := [1, 3, 5, 7, 11, 15, 21, 33, 35, 55, 77, 105, 165, 231, 385, 547, 1155, 1291, 1641, 2735, 3829, 3873, 6017, 6455, 8205, 9037, 11487, 14201, 18051, 19145, 19365, 27111, 30085, 42119, 42603, 45185, 57435, 71005, 90255, 99407, 126357, 135555, 210595, 213015, 298221, 497035, 631785, 706177, 1491105, 2118531, 3530885, 4943239, 7767947, 10592655, 14829717, 23303841, 24716195, 38839735, 54375629, 74148585, 116519205, 163126887, 271878145, 815634435]

theorem mem_divs_iff (d : ℕ) : d ∈ divs ↔ d ∣ 815634435 := by
  have hdiv : (815634435 : ℕ).divisors =
      (3 : ℕ).divisors * (5 : ℕ).divisors * (7 : ℕ).divisors * (11 : ℕ).divisors *
        (547 : ℕ).divisors * (1291 : ℕ).divisors := by
    simp only [← Nat.divisors_mul]
  have h547 : (547 : ℕ).Prime := by norm_num
  have h1291 : (1291 : ℕ).Prime := by norm_num
  rw [Nat.Prime.divisors h547, Nat.Prime.divisors h1291,
    Nat.Prime.divisors (by norm_num : (3 : ℕ).Prime), Nat.Prime.divisors (by norm_num : (5 : ℕ).Prime),
    Nat.Prime.divisors (by norm_num : (7 : ℕ).Prime),
    Nat.Prime.divisors (by norm_num : (11 : ℕ).Prime)] at hdiv
  have hset : ({1, 3} * {1, 5} * {1, 7} * {1, 11} * {1, 547} * {1, 1291} : Finset ℕ) =
      divs.toFinset := by decide
  rw [← Nat.mem_divisors (m := 815634435) |>.trans (and_iff_left (by norm_num)), hdiv, hset,
    List.mem_toFinset]

theorem filter_range_eq :
    (List.range (815634435 + 1)).filter (fun d => decide (d ∣ 815634435)) = divs := by
  apply List.Perm.eq_of_pairwise (le := (· < ·))
  · intro a b _ _ h1 h2; omega
  · exact List.pairwise_lt_range.filter _
  · decide
  · rw [List.perm_ext_iff_of_nodup ((List.nodup_range).filter _) (by decide)]
    intro d
    rw [List.mem_filter, List.mem_range, mem_divs_iff, decide_eq_true_iff]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) h), h⟩

theorem perfectDeficiency_815634435 : perfectDeficiency 815634435 = 6 := by
  unfold perfectDeficiency
  rw [foldl_eq_foldl_filter _ (fun d => decide (d ∣ 815634435)) ?_ , filter_range_eq]
  · decide +kernel
  · intro m d hd
    simp only [decide_eq_false_iff_not] at hd
    simp [hd]

theorem A_815634435 : A 815634435 := ⟨by norm_num, by rw [perfectDeficiency_815634435]; norm_num⟩

set_option maxRecDepth 100000 in
theorem count_A_1156 : Nat.count A 1156 = 59 := by decide +kernel

/-- The conjecture is false: `a (Nat.count A 815634435) = 815634435` is odd. -/
theorem not_conjecture : ¬ ∀ n > 58, Even (a n) := by
  intro h
  have hc : 58 < Nat.count A 815634435 := by
    have := Nat.count_monotone A (show 1156 ≤ 815634435 by norm_num)
    rw [count_A_1156] at this; omega
  have he := h _ hc
  rw [a, Nat.nth_count A_815634435] at he
  exact absurd he (by decide)

#print axioms not_conjecture
-- propext, Classical.choice, Quot.sound
