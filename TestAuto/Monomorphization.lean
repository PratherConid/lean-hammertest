import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Complex.Module
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Order.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Hammertest.DuperInterface

-- Standard TPTP Configs
set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option auto.tptp.solver.name "zeport-fo"
set_option auto.tptp.zeport.path "/home/indprinciples/Programs/zipperposition/portfolio"
-- Standard SMT Configs
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option auto.smt.solver.name "z3"
-- Standard Native Configs
set_option trace.auto.native.printFormulas true
attribute [rebind Auto.Native.solverFunc] Auto.duperRaw

set_option auto.native true
set_option auto.tptp true
/-
section Bug

  open Set

  theorem thm14.auto : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
    intro n
    rw [mem_inter_iff]
    have h₂ : ¬ 2 < 2 := by linarith
    auto [mem_inter_iff,mem_setOf, Nat.Prime.eq_two_or_odd, Nat.even_iff, *]

end Bug

section SimpleClass

set_option auto.redMode "instances"
set_option trace.auto.lamReif.printResult true
set_option trace.auto.lamReif.printValuation true

example (as bs cs ds : List β) : (as ++ bs) ++ (cs ++ ds) = as ++ (bs ++ (cs ++ ds)) := by
  auto [List.append_assoc]

example (as bs cs : List α) (f : α → β) :
  ((as ++ bs) ++ cs).map f = as.map f ++ (bs.map f ++ cs.map f) := by
  auto [List.append_assoc, List.map_append]

set_option auto.redMode "reducible"

set_option trace.auto.printLemmas true in
example (as bs cs ds : List β) : (as ++ bs) ++ (cs ++ ds) = as ++ (bs ++ (cs ++ ds)) := by
  auto [List.append_assoc]

set_option trace.auto.tactic true in
example (as bs cs : List α) (f : α → β) :
  ((as ++ bs) ++ cs).map f = as.map f ++ (bs.map f ++ cs.map f) := by
  auto [List.append_assoc, List.map_append]

end SimpleClass


section SimpleMathlib

set_option auto.redMode "reducible"
set_option trace.auto.lamReif.printResult true
set_option trace.auto.lamReif.printValuation true

-- Testing SynthArg
set_option trace.auto.printLemmas true in
set_option trace.auto.mono.printLemmaInst true in
example (a b : ℝ) (h1 : a < b) : (∃ c, a < c ∧ c < b) := by
  auto [DenselyOrdered.dense, h1]

-- Testing SynthArg
example (a e : ℝ) (h1 : a < e) : (∃ b c d, a < b ∧ b < c ∧ c < d ∧ d < e) := by
  auto [DenselyOrdered.dense, h1]

-- Testing `collectConstInst` correctness
example (m n : Nat) (mlt : m < n) (heq : n = m * (n / m)) : m * 1 < m * (n / m) := by
  duper [mul_one, heq, mlt, lt_of_mul_lt_mul_left] {portfolioInstance := 1}

set_option auto.native false in
set_option trace.auto.printLemmas true in
example (a b c d : ℝ) (h1 : a < b) :
  Set.Icc a b ⊆ Set.Ico c d ↔ c ≤ a ∧ b < d := by
  rw [Set.subset_def]
  auto [Set.mem_Icc, Set.mem_Ico, @le_trans, @le_total, @lt_iff_not_le, h1]

set_option auto.native false in
set_option trace.auto.smt.result true in
example (a b c d : ℝ) (h1 : a < b) : Set.Icc a b ⊆ Set.Ico c d ↔ c ≤ a ∧ b < d := by
  rw [Set.subset_def]
  auto [Set.mem_Icc, Set.mem_Ico, @le_trans, @le_total, @lt_iff_not_le, h1]

set_option auto.native false in
set_option trace.auto.lamReif.printValuation true in
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  auto [Set.subset_def, Set.mem_image, Set.mem_preimage]

set_option auto.native false in
example (h : Function.Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  auto [Set.subset_def, Set.mem_preimage, Function.Injective.mem_set_image, h]

set_option auto.native false in
example : f '' (f ⁻¹' u) ⊆ u := by
  auto [Set.subset_def, Set.mem_image, Set.mem_preimage]

set_option auto.native false in
example (h : Function.Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  auto [Set.subset_def, Set.mem_image, Set.mem_preimage, h] d[Function.Surjective]

end SimpleMathlib



section Chebyshev

/-!
# Multiple angle formulas in terms of Chebyshev polynomials

This file gives the trigonometric characterizations of Chebyshev polynomials, for both the real
(`Real.cos`) and complex (`Complex.cos`) cosine.
-/

namespace Polynomial.Chebyshev

open Polynomial

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-! ### Complex versions -/

section Complex

open Complex

variable (θ : ℂ)

set_option profiler true
set_option trace.auto.lamReif.printProofs true
set_option trace.auto.tptp.result true

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
@[simp]
theorem T_complex_cos : ∀ (n : ℕ), (T ℂ n).eval (cos θ) = cos (n * θ)
  | 0 => by auto [T_zero, eval_one, Nat.cast_zero, zero_mul, cos_zero]
  | 1 => by auto [eval_X, one_mul, T_one, Nat.cast_one]
  | n + 2 => by
    rw [Nat.cast_add, Nat.cast_two, T_add_two];
    have eval_two : eval (cos θ) 2 = (2 : ℕ) := by norm_num
    simp only [eval_sub, eval_mul, eval_X, eval_two]
    have norm_n_plus_one : (↑n : Int) + 1 = ↑(n + 1) := rfl
    rw [norm_n_plus_one, T_complex_cos n, T_complex_cos (n + 1)]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_two, add_mul,
      cos_add, one_mul, mul_assoc, sin_two_mul, cos_two_mul]
    simp only [mul_sub, pow_two, mul_one]
    auto [sub_right_comm, mul_comm, mul_assoc]

theorem T_complex_cos' : ∀ (n : ℕ), (T ℂ n).eval (cos θ) = cos (n * θ)
  | 0 => by auto [T_zero, eval_one, Nat.cast_zero, zero_mul, cos_zero]
  | 1 => by auto [eval_X, one_mul, T_one, Nat.cast_one]
  | n + 2 => by
    rw [Nat.cast_add, Nat.cast_two, T_add_two];
    have eval_two : eval (cos θ) 2 = (2 : ℕ) := by norm_num
    simp only [eval_sub, eval_mul, eval_X, eval_two]
    have norm_n_plus_one : (↑n : Int) + 1 = ↑(n + 1) := rfl
    rw [norm_n_plus_one, T_complex_cos' n, T_complex_cos' (n + 1)]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_two, add_mul,
      cos_add, one_mul, mul_assoc, sin_two_mul, cos_two_mul]
    simp only [mul_sub, sub_right_comm, mul_one]
    auto [pow_two, mul_comm, mul_assoc]

set_option auto.tptp false

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
theorem U_complex_cos (n : ℕ) : (U ℂ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) := by
  induction' n with d hd
  -- `auto` fails if we provide `CharP.cast_eq_zero` instead of `CharP.cast_eq_zero _ Nat.zero`
  · auto [U_zero, eval_one, zero_add, one_mul, Nat.zero_eq, CharP.cast_eq_zero _ Nat.zero]
  · have u_norm : U ℂ ↑(d + 1) = U ℂ (↑d + 1) := rfl
    rw [u_norm, U_eq_X_mul_U_add_T]
    have t_norm : T ℂ (↑d + 1) = T ℂ ↑(d + 1) := rfl
    simp only [t_norm, eval_add, T_complex_cos, eval_mul, eval_X,
      add_mul _ _ (sin θ), mul_assoc, hd]
    have add_one_one_norm : (↑(d + 1) + 1) * θ = ↑(d + 1) * θ + θ := by
      simp only [add_mul, one_mul]
    rw [add_one_one_norm, sin_add (↑(d + 1) * θ)]; push_cast
    auto [add_mul, one_mul, mul_comm]

end Complex

end Polynomial.Chebyshev

end Chebyshev
-/

section ShortFive

open Function

structure is_short_exact {A B C : Type _} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A → B) (g : B → C) :=
  (inj       : Injective f)
  (im_in_ker : ∀ a : A, g (f a) = 0)
  (ker_in_im : ∀ b : B, g b = 0 → ∃ a : A, f a = b)
  (surj      : Surjective g)

variable {A₀ B₀ C₀ A₁ B₁ C₁ : Type _}
variable [AddCommGroup A₀] [AddCommGroup B₀] [AddCommGroup C₀]
variable [AddCommGroup A₁] [AddCommGroup B₁] [AddCommGroup C₁]

variable {f₀ : A₀ →+ B₀} {g₀ : B₀ →+ C₀}
variable {f₁ : A₁ →+ B₁} {g₁ : B₁ →+ C₁}
variable {h  : A₀ →+ A₁} {k  : B₀ →+ B₁} {l  : C₀ →+C₁}

variable (short_exact₀ : is_short_exact f₀ g₀)
variable (short_exact₁ : is_short_exact f₁ g₁)
variable (square₀      : ∀ a, k (f₀ a) = f₁ (h a))
variable (square₁      : ∀ b, l (g₀ b) = g₁ (k b))

open is_short_exact

set_option profiler true
set_option trace.auto.lamReif.printProofs true

set_option auto.mono.saturationThreshold 500
def short_five_mono (injh : Injective h) (injl : Injective l) :
    Injective k := by
  auto [injective_iff_map_eq_zero, injl, injh, short_exact₁.inj,
       square₀, square₁, short_exact₀.ker_in_im, map_zero] u[Injective]

def short_five_epi (surjh : Surjective h) (surjl : Surjective l) :
    Surjective k := by
  intro b₁
  rcases surjl (g₁ b₁) with ⟨c₀, hlc₀⟩
  rcases short_exact₀.surj c₀ with ⟨b₀, hg₀b₀⟩
  have : g₁ (k b₀ - b₁) = 0 := by
    auto [map_sub, square₁, hg₀b₀, hlc₀, sub_self]
  rcases short_exact₁.ker_in_im _ this with ⟨a₁, hf₁a₁⟩
  auto [map_sub, square₀, surjh a₁, hf₁a₁, sub_sub_cancel]

end ShortFive
