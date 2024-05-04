import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Nat.Parity
import Hammertest.DuperInterface

set_option warningAsError false

-- Standard Preprocessing Configs
set_option auto.redMode "reducible"
-- Standard TPTP Configs
set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option auto.tptp.solver.name "zeport-lams"
set_option auto.tptp.zeport.path "/home/indprinciple/Programs/zipperposition/portfolio"
-- Standard SMT Configs
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option auto.smt.solver.name "z3"
set_option auto.smt.trust true
-- Standard Native Configs
set_option trace.auto.native.printFormulas true
set_option auto.native.solver.func "Auto.duperRaw"

set_option auto.native true
set_option trace.auto.lamReif.printResult true
set_option trace.auto.lamReif.printValuation true

set_option trace.auto.tptp.premiseSelection true

def autoFailSorry := sorryAx

def tptpSuccessSorry := sorryAx

def Nat.dvd_def (a b : Nat) : Dvd.dvd a b = (∃ c, b = a * c) := rfl

namespace Introduction

  theorem easy : 2 + 2 = 4 :=
    rfl

  theorem easy.auto : 2 + 2 = 4 := by
    auto

  theorem thm1 : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
    have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
    show ∃ l, m * n = l + l from ⟨_, hmn⟩

  theorem thm1.auto : ∀ m n : Nat, Even n → Even (m * n) := by
    auto [mul_add] d[Even]

end Introduction


namespace Basics

  theorem thm1 (a b c : ℝ) : a * b * c = b * (a * c) := by
    rw [mul_comm a b]
    rw [mul_assoc b a c]

  theorem thm1.auto (a b c : ℝ) : a * b * c = b * (a * c) := by
    auto [mul_comm, mul_assoc]

  theorem thm2 (a b c : ℝ) : c * b * a = b * (a * c) := by
    rw [mul_comm c b]
    rw [mul_assoc b c a]
    rw [mul_comm c a]

  theorem thm2.auto (a b c : ℝ) : a * (b * c) = b * (a * c) := by
    auto [mul_comm, mul_assoc]

  theorem thm3 (a b c : ℝ) : a * b * c = b * c * a := by
    rw [mul_assoc]
    rw [mul_comm]

  theorem thm3.auto (a b c : ℝ) : a * b * c = b * c * a := by
    auto [mul_assoc, mul_comm]

  theorem thm4 (a b c : ℝ) : a * (b * c) = b * (c * a) := by
    rw [mul_comm]
    rw [mul_assoc]

  theorem thm4.auto (a b c : ℝ) : a * (b * c) = b * (c * a) := by
    auto [mul_comm, mul_assoc]

  theorem thm5 (a b c : ℝ) : a * (b * c) = b * (a * c) := by
    rw [← mul_assoc]
    rw [mul_comm a]
    rw [mul_assoc]

  theorem thm5.auto (a b c : ℝ) : a * (b * c) = b * (a * c) := by
    auto [mul_comm, mul_assoc]

  theorem thm6 (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
    rw [h']
    rw [← mul_assoc]
    rw [h]
    rw [mul_assoc]

  theorem thm6.auto (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
    auto [mul_assoc, *]

  theorem thm7 (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
    rw [mul_assoc a]
    rw [h]
    rw [← mul_assoc]

  theorem thm7.auto (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
    auto [mul_assoc, *]

  theorem thm8 (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
    rw [hyp]
    rw [hyp']
    rw [mul_comm]
    rw [sub_self]

  theorem thm8.auto (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
    auto [mul_comm, sub_self, *]

  theorem thm9 (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
    rw [h', ← mul_assoc, h, mul_assoc]

  theorem thm9.auto (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
    auto [mul_assoc, *]

  section
  variable (a b : ℝ)

  theorem thm10 : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
    rw [mul_add, add_mul, add_mul]
    rw [← add_assoc, add_assoc (a * a)]
    rw [mul_comm b a, ← two_mul]

  set_option auto.smt true in
  theorem thm10.auto : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
    auto [mul_add, add_mul, add_assoc, mul_comm, two_mul]

  end

  section
  variable (a b c d : ℝ)

  theorem thm11 : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
    rw [add_mul, mul_add, mul_add, ← add_assoc (a * c + a * d)]

  theorem thm11.auto : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
    auto [add_mul, mul_add, add_assoc]

  theorem thm12 (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
    rw [mul_sub, add_mul, add_mul, mul_comm b a]
    rw [← sub_sub, ← add_sub, sub_self, add_zero]
    rw [pow_two, pow_two]

  set_option auto.smt true in
  theorem thm12.auto (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
    auto [mul_sub, add_mul, mul_comm, sub_sub, add_sub, sub_self, add_zero, pow_two]

  end

  section
  variable (a b c d : ℝ)

  theorem thm13 (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
    rw [hyp'] at hyp
    rw [mul_comm d a] at hyp
    rw [← two_mul (a * d)] at hyp
    rw [← mul_assoc 2 a d] at hyp
    exact hyp

  theorem thm13.auto (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
    auto [mul_comm, two_mul, mul_assoc, *]

  end

  theorem thm14 (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
    nth_rw 2 [h]
    rw [add_mul]

  theorem thm14.auto (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
    auto [add_mul, *]

  namespace MyRing
  variable {R : Type*} [Ring R]

  theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

  theorem add_zero.auto (a : R) : a + 0 = a := by auto [add_comm, zero_add]

  theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, add_left_neg]

  theorem add_right_neg.auto (a : R) : a + -a = 0 := by auto [add_comm, add_left_neg]

  end MyRing

  namespace MyRing
  variable {R : Type*} [Ring R]

  theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
    rw [← add_assoc, add_left_neg, zero_add]

  theorem neg_add_cancel_left.auto (a b : R) : -a + (a + b) = b := by
    auto [add_assoc, add_left_neg, zero_add]

  theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
    rw [add_assoc, add_right_neg, add_zero]

  theorem add_neg_cancel_right.auto (a b : R) : a + b + -b = a := by
    auto [add_assoc, add_right_neg, add_zero]

  theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
    rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

  theorem add_left_cancel.auto {a b c : R} (h : a + b = a + c) : b = c := by
    auto [h, neg_add_cancel_left]

  theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
    rw [← add_neg_cancel_right a b, h, add_neg_cancel_right]

  theorem add_right_cancel.auto {a b c : R} (h : a + b = c + b) : a = c := by
    auto [h, add_neg_cancel_right]

  theorem mul_zero (a : R) : a * 0 = 0 := by
    have h : a * 0 + a * 0 = a * 0 + 0 := by
      rw [← mul_add, add_zero, add_zero]
    rw [add_left_cancel h]

  theorem mul_zero.auto (a : R) : a * 0 = 0 := by
    auto [add_left_cancel, mul_add, add_zero]

  theorem zero_mul (a : R) : 0 * a = 0 := by
    have h : 0 * a + 0 * a = 0 * a + 0 := by rw [← add_mul, add_zero, add_zero]
    rw [add_left_cancel h]

  theorem zero_mul.auto (a : R) : 0 * a = 0 := by
    auto [add_left_cancel, add_mul, add_zero]

  theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
    rw [← neg_add_cancel_left a b, h, add_zero]

  theorem neg_eq_of_add_eq_zero.auto {a b : R} (h : a + b = 0) : -a = b := by
    auto [neg_add_cancel_left, h, add_zero]

  theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
    symm
    apply neg_eq_of_add_eq_zero
    rw [add_comm, h]

  theorem eq_neg_of_add_eq_zero.auto {a b : R} (h : a + b = 0) : a = -b := by
    auto [neg_eq_of_add_eq_zero, add_comm, h]

  theorem neg_zero : (-0 : R) = 0 := by
    apply neg_eq_of_add_eq_zero
    rw [add_zero]

  theorem neg_zero.auto : (-0 : R) = 0 := by
    auto [neg_eq_of_add_eq_zero, add_zero]

  theorem neg_neg (a : R) : - -a = a := by
    apply neg_eq_of_add_eq_zero
    rw [add_left_neg]

  theorem neg_neg.auto (a : R) : - -a = a := by
    auto [neg_eq_of_add_eq_zero, add_left_neg]

  end MyRing

  namespace MyRing
  variable {R : Type*} [Ring R]

  theorem self_sub (a : R) : a - a = 0 := by
    rw [sub_eq_add_neg, add_right_neg]

  theorem self_sub.auto (a : R) : a - a = 0 := by
    auto [sub_eq_add_neg, add_right_neg]

  theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
    norm_num

  theorem one_add_one_eq_two.auto : 1 + 1 = (2 : R) := autoFailSorry _

  theorem two_mul (a : R) : 2 * a = a + a := by
    rw [← one_add_one_eq_two, add_mul, one_mul]

  theorem two_mul.auto (a : R) : 2 * a = a + a := by
    auto [one_add_one_eq_two, add_mul, one_mul]

  end MyRing

  section
  variable {G : Type*} [Group G]

  namespace MyGroup

  theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
    have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
      rw [mul_assoc, ← mul_assoc a⁻¹ a, mul_left_inv, one_mul, mul_left_inv]
    rw [← h, ← mul_assoc, mul_left_inv, one_mul]

  theorem mul_right_inv.auto (a : G) : a * a⁻¹ = 1 := by
    auto [mul_assoc, mul_left_inv, one_mul]

  theorem mul_one (a : G) : a * 1 = a := by
    rw [← mul_left_inv a, ← mul_assoc, mul_right_inv, one_mul]

  theorem mul_one.auto (a : G) : a * 1 = a := by
    auto [mul_left_inv, mul_assoc, mul_right_inv, one_mul]

  theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
    rw [← one_mul (b⁻¹ * a⁻¹), ← mul_left_inv (a * b), mul_assoc, mul_assoc, ← mul_assoc b b⁻¹,
      mul_right_inv, one_mul, mul_right_inv, mul_one]

  set_option auto.smt true in
  theorem mul_inv_rev.auto (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
    auto [one_mul, mul_left_inv, mul_right_inv, mul_assoc]

  end MyGroup

  end

  section UsingThmsAndLemmas

  variable (a b c d e : ℝ)
  open Real

  theorem thm15 (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
    apply lt_of_le_of_lt h₀
    apply lt_trans h₁
    exact lt_of_le_of_lt h₂ h₃

  theorem thm15.auto (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
    auto [lt_of_le_of_lt, lt_trans, *]

  theorem thm16 (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
    apply add_le_add_left
    rw [exp_le_exp]
    apply add_le_add_left h₀

  theorem thm16.auto (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
    auto [add_le_add_left, exp_le_exp, *]

  theorem thm17 (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
    have h₀ : 0 < 1 + exp a := by linarith [exp_pos a]
    apply log_le_log h₀
    apply add_le_add_left (exp_le_exp.mpr h)

  theorem thm17.auto (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
    have h₀ : 0 < 1 + exp a := by linarith [exp_pos a]
    auto [log_le_log, add_le_add_left, exp_le_exp, *]

  theorem thm18 (h : a ≤ b) : c - exp b ≤ c - exp a := by
    apply sub_le_sub_left
    exact exp_le_exp.mpr h

  theorem thm18.auto (h : a ≤ b) : c - exp b ≤ c - exp a := by
    auto [sub_le_sub_left, exp_le_exp, *]

  theorem thm19 : a * b * 2 ≤ a ^ 2 + b ^ 2 := by
    have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
    calc
      a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
      _ ≥ 0 := by apply pow_two_nonneg
    linarith

  theorem thm19.auto : a * b * 2 ≤ a ^ 2 + b ^ 2 := autoFailSorry _

  theorem thm20 : -(a * b) * 2 ≤ a ^ 2 + b ^ 2 := by
    have h : 0 ≤ a ^ 2 + 2 * a * b + b ^ 2
    calc
      a ^ 2 + 2 * a * b + b ^ 2 = (a + b) ^ 2 := by ring
      _ ≥ 0 := by apply pow_two_nonneg
    linarith

  theorem thm20.auto : -(a * b) * 2 ≤ a ^ 2 + b ^ 2 := autoFailSorry _

  theorem thm21 : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    have h : (0 : ℝ) < 2 := by norm_num
    apply abs_le'.mpr
    constructor
    · rw [le_div_iff h]
      apply thm19
    rw [le_div_iff h]
    apply thm20

  theorem thm21.auto : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    have h : (0 : ℝ) < 2 := by norm_num
    auto [abs_le', le_div_iff, thm19, thm20, h]

  end UsingThmsAndLemmas

  section
  variable (a b c d : ℝ)

  theorem thm22 : min a b = min b a := by
    apply le_antisymm
    · show min a b ≤ min b a
      apply le_min
      · apply min_le_right
      apply min_le_left
    · show min b a ≤ min a b
      apply le_min
      · apply min_le_right
      apply min_le_left

  theorem thm22.auto : min a b = min b a := by
    auto [le_antisymm, le_min, min_le_left, min_le_right]

  theorem thm23 : max a b = max b a := by
    apply le_antisymm
    repeat
      apply max_le
      apply le_max_right
      apply le_max_left

  theorem thm23.auto : max a b = max b a := by
    auto [le_antisymm, max_le, le_max_right, le_max_left]

  theorem thm24 : min (min a b) c = min a (min b c) := by
    apply le_antisymm
    · apply le_min
      · apply le_trans
        apply min_le_left
        apply min_le_left
      apply le_min
      · apply le_trans
        apply min_le_left
        apply min_le_right
      apply min_le_right
    apply le_min
    · apply le_min
      · apply min_le_left
      apply le_trans
      apply min_le_right
      apply min_le_left
    apply le_trans
    apply min_le_right
    apply min_le_right

  set_option auto.smt true in
  theorem thm24.auto : min (min a b) c = min a (min b c) := by
    auto [le_antisymm, le_min, le_trans, min_le_left, min_le_right]

  theorem aux : min a b + c ≤ min (a + c) (b + c) := by
    apply le_min
    · apply add_le_add_right
      apply min_le_left
    apply add_le_add_right
    apply min_le_right

  theorem aux.auto : min a b + c ≤ min (a + c) (b + c) := by
    auto [le_min, add_le_add_right, min_le_left, min_le_right]

  theorem thm25 : min a b + c = min (a + c) (b + c) := by
    apply le_antisymm
    · apply aux
    have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
    rw [h]
    apply add_le_add_right
    rw [sub_eq_add_neg]
    apply le_trans
    apply aux
    rw [add_neg_cancel_right, add_neg_cancel_right]

  theorem thm25.auto : min a b + c = min (a + c) (b + c) := by
    auto [le_antisymm, le_trans, aux, add_le_add_right, sub_eq_add_neg, add_neg_cancel_right]

  theorem thm26 : |a| - |b| ≤ |a - b| :=
    calc
      |a| - |b| = |a - b + b| - |b| := by rw [sub_add_cancel]
      _ ≤ |a - b| + |b| - |b| := by
        apply sub_le_sub_right
        apply abs_add
      _ ≤ |a - b| := by rw [add_sub_cancel]

  theorem thm26.auto : |a| - |b| ≤ |a - b| := by
    auto [sub_add_cancel, sub_le_sub_right, abs_add, add_sub_cancel]

  end

  section
  variable (w x y z : ℕ)

  theorem thm27 : x ∣ y * x * z := by
    apply dvd_mul_of_dvd_left
    apply dvd_mul_left

  theorem thm27.auto : x ∣ y * x * z := by
    auto [dvd_mul_of_dvd_left, dvd_mul_left]

  theorem thm28 : x ∣ x ^ 2 := by
    apply dvd_mul_left

  theorem thm28.auto : x ∣ x ^ 2 := by
    auto [pow_two, dvd_mul_left]

  theorem thm29 (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
    apply dvd_add
    · apply dvd_add
      · apply dvd_mul_of_dvd_right
        apply dvd_mul_right
      apply dvd_mul_left
    rw [pow_two]
    apply dvd_mul_of_dvd_right
    exact h

  theorem thm29.auto (_ : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 :=
    autoFailSorry _

  end

  theorem thm30 (m n : ℕ) : Nat.gcd m n = Nat.gcd n m := by
    apply Nat.dvd_antisymm
    repeat'
      apply Nat.dvd_gcd
      apply Nat.gcd_dvd_right
      apply Nat.gcd_dvd_left

  theorem thm30.auto (m n : ℕ) : Nat.gcd m n = Nat.gcd n m := by
    auto [Nat.dvd_antisymm, Nat.dvd_gcd, Nat.gcd_dvd_left, Nat.gcd_dvd_right]

  section
  variable {α : Type*} [Lattice α]
  variable (x y z : α)

  theorem thm31 : x ⊓ y = y ⊓ x := by
    apply le_antisymm
    repeat'
      apply le_inf
      · apply inf_le_right
      apply inf_le_left

  theorem thm31.auto : x ⊓ y = y ⊓ x := by
    auto [le_antisymm, le_inf, inf_le_left, inf_le_right]

  theorem thm32 : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
    apply le_antisymm
    · apply le_inf
      · apply le_trans
        apply inf_le_left
        apply inf_le_left
      apply le_inf
      · apply le_trans
        apply inf_le_left
        apply inf_le_right
      apply inf_le_right
    apply le_inf
    · apply le_inf
      · apply inf_le_left
      apply le_trans
      apply inf_le_right
      apply inf_le_left
    apply le_trans
    apply inf_le_right
    apply inf_le_right

  set_option auto.smt true in
  theorem thm32.auto : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
    auto [le_antisymm, le_inf, le_trans, inf_le_left, inf_le_right]

  theorem thm33 : x ⊔ y = y ⊔ x := by
    apply le_antisymm
    repeat'
      apply sup_le
      · apply le_sup_right
      apply le_sup_left

  theorem thm33.auto : x ⊔ y = y ⊔ x := by
    auto [le_antisymm, sup_le, le_sup_left, le_sup_right]

  theorem thm34 : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
    apply le_antisymm
    · apply sup_le
      · apply sup_le
        apply le_sup_left
        · apply le_trans
          apply @le_sup_left _ _ y z
          apply le_sup_right
      apply le_trans
      apply @le_sup_right _ _ y z
      apply le_sup_right
    apply sup_le
    · apply le_trans
      apply @le_sup_left _ _ x y
      apply le_sup_left
    apply sup_le
    · apply le_trans
      apply @le_sup_right _ _ x y
      apply le_sup_left
    apply le_sup_right

  set_option auto.smt true in
  theorem thm34.auto : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
    auto [le_antisymm, sup_le, le_sup_left, le_sup_right, le_trans]

  theorem absorb1 : x ⊓ (x ⊔ y) = x := by
    apply le_antisymm
    · apply inf_le_left
    apply le_inf
    · apply le_refl
    apply le_sup_left

  theorem absorb1.auto : x ⊓ (x ⊔ y) = x := by
    auto [le_antisymm, inf_le_left, le_inf, le_refl, le_sup_left]

  theorem absorb2 : x ⊔ x ⊓ y = x := by
    apply le_antisymm
    · apply sup_le
      · apply le_refl
      apply inf_le_left
    apply le_sup_left

  theorem absorb2.auto : x ⊔ x ⊓ y = x := by
    auto [le_antisymm, sup_le, le_refl, inf_le_left, le_sup_left]

  end

  section
  variable {α : Type*} [Lattice α]
  variable (a b c : α)

  theorem thm35 (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
    rw [h, @inf_comm _ _ (a ⊔ b), absorb1, @inf_comm _ _ (a ⊔ b), h, ← sup_assoc, @inf_comm _ _ c a,
      absorb2, inf_comm]

  set_option auto.smt true in
  theorem thm35.auto (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
    auto [h, inf_comm, sup_assoc, absorb1, absorb2]

  theorem thm36 (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
    rw [h, @sup_comm _ _ (a ⊓ b), absorb2, @sup_comm _ _ (a ⊓ b), h, ← inf_assoc, @sup_comm _ _ c a,
      absorb1, sup_comm]

  set_option auto.smt true in
  theorem thm36.auto (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
    auto [h, sup_comm, inf_assoc, absorb1, absorb2]

  end

  section
  variable {R : Type*} [StrictOrderedRing R]
  variable (a b c : R)

  theorem aux1 (h : a ≤ b) : 0 ≤ b - a := by
    rw [← sub_self a, sub_eq_add_neg, sub_eq_add_neg, add_comm, add_comm b]
    apply add_le_add_left h

  theorem aux1.auto (h : a ≤ b) : 0 ≤ b - a := by
    auto [sub_self, sub_eq_add_neg, add_comm, add_le_add_left, h]

  theorem aux2 (h : 0 ≤ b - a) : a ≤ b := by
    rw [← add_zero a, ← sub_add_cancel b a, add_comm (b - a)]
    apply add_le_add_left h

  theorem aux2.auto (h : 0 ≤ b - a) : a ≤ b := by
    auto [add_zero, sub_add_cancel, add_comm, add_le_add_left, h]

  theorem thm37 (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
    have h1 : 0 ≤ (b - a) * c := mul_nonneg (aux1 _ _ h) h'
    rw [sub_mul] at h1
    exact aux2 _ _ h1

  theorem thm37.auto (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
    auto [mul_nonneg, sub_mul, aux1, aux2, *]

  end

  section
  variable {X : Type*} [MetricSpace X]
  variable (x y z : X)

  theorem thm38 (x y : X) : 0 ≤ dist x y := by
    have : 0 ≤ dist x y + dist y x := by
      rw [← dist_self x]
      apply dist_triangle
    linarith [dist_comm x y]

  theorem thm38.auto (x y : X) : 0 ≤ dist x y := by
    have : ∀ (x : ℝ), 0 ≤ x + x → 0 ≤ x := by intros; linarith
    auto [dist_self, dist_triangle, dist_comm, *]

  end

end Basics



namespace Logic

  theorem my_lemma :
      ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
    intro x y ε epos ele1 xlt ylt
    calc
      |x * y| = |x| * |y| := by apply abs_mul
      _ ≤ |x| * ε := by apply mul_le_mul; linarith; linarith; apply abs_nonneg; apply abs_nonneg;
      _ < 1 * ε := by rw [mul_lt_mul_right epos]; linarith
      _ = ε := by apply one_mul

  theorem my_lemma.auto :
      ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
    auto [abs_mul, mul_one, le_of_lt, lt_of_lt_of_le, lt_of_le_of_lt, le_refl, mul_le_mul, abs_nonneg]

  def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
    ∀ x, f x ≤ a

  def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
    ∀ x, a ≤ f x

  section
  variable (f g : ℝ → ℝ) (a b : ℝ)

  theorem thm1 (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
    intro x
    dsimp
    apply add_le_add
    apply hfa
    apply hgb

  theorem thm1.auto (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
    auto [add_le_add, *] d[FnUb]

  theorem thm2 (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
    intro x
    apply add_le_add
    apply hfa
    apply hgb

  theorem thm2.auto (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
    auto [add_le_add, *] d[FnLb]

  theorem thm3 (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
    intro x
    apply mul_nonneg
    apply nnf
    apply nng

  theorem thm3.auto (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
    auto [mul_nonneg, *] d[FnLb]

  theorem thm4 (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
      FnUb (fun x ↦ f x * g x) (a * b) := by
    intro x
    apply mul_le_mul
    apply hfa
    apply hgb
    apply nng
    apply nna

  theorem thm4.auto (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
      FnUb (fun x ↦ f x * g x) (a * b) := by
    auto [mul_le_mul, *] d[FnUb, FnLb]

  end

  section
  variable (f g : ℝ → ℝ)

  theorem thm5 (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
    fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)

  theorem thm5.auto (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
    auto [add_le_add, *] d[Monotone]

  theorem thm6 {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
    fun a b aleb ↦ mul_le_mul_of_nonneg_left (mf aleb) nnc

  theorem thm6.auto {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
    auto [mul_le_mul_of_nonneg_left, *] d[Monotone]

  theorem thm7 (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
    fun a b aleb ↦ mf (mg aleb)

  theorem thm7.auto (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
    auto [*] d[Monotone]

  def FnEven (f : ℝ → ℝ) : Prop :=
    ∀ x, f x = f (-x)

  def FnOdd (f : ℝ → ℝ) : Prop :=
    ∀ x, f x = -f (-x)

  theorem thm8 (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
    intro x
    calc
      (fun x ↦ f x + g x) x = f x + g x := rfl
      _ = f (-x) + g (-x) := by rw [ef, eg]

  theorem thm8.auto (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
    auto [*] d[FnEven]

  theorem thm9 (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
    intro x
    calc
      (fun x ↦ f x * g x) x = f x * g x := rfl
      _ = f (-x) * g (-x) := by rw [of, og, neg_mul_neg]

  theorem thm9.auto (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
    auto [neg_mul_neg, *] d[FnOdd, FnEven]

  theorem thm10 (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
    intro x
    dsimp
    rw [ef, og, neg_mul_eq_mul_neg]

  theorem thm10.auto (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
    auto [*, neg_mul_eq_mul_neg] d[FnEven, FnOdd]

  theorem thm11 (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
    intro x
    dsimp
    rw [og, ← ef]

  theorem thm11.auto (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
    auto [*] d[FnEven, FnOdd]

  end

  section

  variable {α : Type*} (r s t : Set α)

  theorem Subset.refl : s ⊆ s := fun x xs ↦ xs

  theorem Subset.refl.auto : s ⊆ s := by intro; auto

  theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t :=
    fun rsubs ssubt x xr ↦ ssubt (rsubs xr)

  theorem Subset.trans.auto : r ⊆ s → s ⊆ t → r ⊆ t := by
    auto [Set.subset_def]

  end

  section
  variable {α : Type*} [PartialOrder α]
  variable (s : Set α) (a b : α)

  def SetUb (s : Set α) (a : α) :=
    ∀ x, x ∈ s → x ≤ a

  theorem thm12 (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
    fun x xs ↦ le_trans (h x xs) h'

  theorem thm12.auto (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
    auto [le_trans, *] d[SetUb]

  end

  section

  open Function

  theorem thm13 (c : ℝ) : Injective fun x ↦ x + c := by
    intro x₁ x₂ h'
    exact (add_left_inj c).mp h'

  theorem thm13.auto (c : ℝ) : Injective fun x ↦ x + c := by
    auto [add_left_inj] d[Injective]

  theorem thm14 {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
    intro x₁ x₂ h'
    apply (mul_right_inj' h).mp h'

  theorem thm14.auto {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
    auto [mul_right_inj', *] d[Injective]

  variable {α : Type*} {β : Type*} {γ : Type*}
  variable {g : β → γ} {f : α → β}

  theorem thm15 (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
    intro x₁ x₂ h
    apply injf
    apply injg
    apply h

  theorem thm15.auto (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
    auto [*] d[Injective]

  end

  def FnHasUb (f : ℝ → ℝ) :=
    ∃ a, FnUb f a

  def FnHasLb (f : ℝ → ℝ) :=
    ∃ a, FnLb f a

  theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
      FnUb (fun x ↦ f x + g x) (a + b) :=
    fun x ↦ add_le_add (hfa x) (hgb x)

  theorem fnUb_add.auto {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
      FnUb (fun x ↦ f x + g x) (a + b) := by
    auto [*, add_le_add] d[FnUb]

  section

  variable {f g : ℝ → ℝ}

  theorem thm16 (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
    rcases ubf with ⟨a, ubfa⟩
    rcases ubg with ⟨b, ubgb⟩
    use a + b
    apply fnUb_add ubfa ubgb

  theorem thm16.auto (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
    auto [add_le_add, *] d[FnHasUb, FnUb]

  theorem thm17 {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
    rcases ubf with ⟨a, ubfa⟩
    use c * a
    intro x
    exact mul_le_mul_of_nonneg_left (ubfa x) h

  theorem thm17.auto {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
    auto [*, mul_le_mul_of_nonneg_left] d[FnHasUb, FnUb]

  theorem thm18 : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
    rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
    exact ⟨a + b, fnUb_add ubfa ubgb⟩

  theorem thm18.auto : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
    auto [add_le_add, *] d[FnHasUb, FnUb]

  end

  section

  variable {α : Type*} [CommRing α]

  def SumOfSquares (x : α) :=
    ∃ a b, x = a ^ 2 + b ^ 2

  theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
      SumOfSquares (x * y) := by
    rcases sosx with ⟨a, b, xeq⟩
    rcases sosy with ⟨c, d, yeq⟩
    rw [xeq, yeq]
    use a * c - b * d, a * d + b * c
    ring

  theorem sumOfSquares_mul.auto {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
    have (a b c d : α) : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by ring
    auto [*] d[SumOfSquares]

  end

  section
  variable {a b c : ℕ}

  theorem thm19 (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
    rcases divab with ⟨d, beq⟩
    rcases divbc with ⟨e, ceq⟩
    rw [ceq, beq]
    use d * e; ring

  theorem thm19.auto (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
    auto [mul_assoc, Nat.dvd_def, *]

  theorem thm20 (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
    rcases divab with ⟨d, rfl⟩
    rcases divac with ⟨e, rfl⟩
    use d + e; ring

  theorem thm20.auto (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
    auto [Nat.dvd_def, mul_add, *]

  end

  section

  open Function

  theorem thm21 {c : ℝ} : Surjective fun x ↦ x + c := by
    intro x
    use x - c
    dsimp; ring

  theorem thm21.auto {c : ℝ} : Surjective fun x ↦ x + c := by
    auto [sub_add_cancel] d[Surjective]

  theorem thm22 {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
    intro x
    use x / c
    dsimp; rw [mul_comm, div_mul_cancel _ h]

  theorem thm22.auto {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
    auto [mul_comm, div_mul_cancel, h] d[Surjective]

  theorem thm23 (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
    field_simp [h]
    ring

  theorem thm23.auto (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := autoFailSorry _

  theorem thm24 {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
    rcases h 2 with ⟨x, hx⟩
    use x
    rw [hx]
    norm_num

  theorem thm24.auto {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
    auto [show (2 : ℝ) ^ 2 = 4 by norm_num, h] d[Surjective]

  end

  section
  open Function
  variable {α : Type*} {β : Type*} {γ : Type*}
  variable {g : β → γ} {f : α → β}

  theorem thm25 (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
    intro z
    rcases surjg z with ⟨y, rfl⟩
    rcases surjf y with ⟨x, rfl⟩
    use x

  theorem thm25.auto (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
    auto [*] d[Surjective]

  end

  section
  variable (a b : ℝ)

  theorem thm26 (h : a < b) : ¬b < a := by
    intro h'
    have : a < a := lt_trans h h'
    apply lt_irrefl a this

  theorem thm26.auto (h : a < b) : ¬b < a := by
    auto [lt_trans, lt_irrefl, h]

  variable (f : ℝ → ℝ)

  theorem thm27 (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
    intro fnub
    rcases fnub with ⟨a, fnuba⟩
    rcases h a with ⟨x, hx⟩
    have : f x ≤ a := fnuba x
    linarith

  theorem thm27.auto (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
    auto [h, not_le] d[FnHasUb, FnUb]

  theorem thm28 (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
    rintro ⟨a, ha⟩
    rcases h a with ⟨x, hx⟩
    have := ha x
    linarith

  theorem thm28.auto (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
    auto [h, not_le] d[FnHasLb, FnLb]

  theorem thm29 : ¬FnHasUb fun x ↦ x := by
    rintro ⟨a, ha⟩
    have : a + 1 ≤ a := ha (a + 1)
    linarith

  theorem thm29.auto : ¬FnHasUb fun x ↦ x := by
    have (a : ℝ) : ¬ (a + 1 ≤ a) := by linarith
    auto [*] d[FnHasUb, FnUb]

  theorem thm30 (h : Monotone f) (h' : f a < f b) : a < b := by
    apply lt_of_not_ge
    intro h''
    apply absurd h'
    apply not_lt_of_ge (h h'')

  theorem thm30.auto (h : Monotone f) (h' : f a < f b) : a < b := by
    auto [lt_of_not_ge, not_lt_of_ge, *] d[Monotone]

  theorem thm31 (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
    intro h''
    apply absurd h'
    apply not_lt_of_ge
    apply h'' h

  theorem thm31.auto (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
    auto [not_lt_of_ge, *] d[Monotone]

  theorem thm32 : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
    intro h
    let f := fun x : ℝ ↦ (0 : ℝ)
    have monof : Monotone f := by
      intro a b leab
      rfl
    have h' : f 1 ≤ f 0 := le_refl _
    have : (1 : ℝ) ≤ 0 := h monof h'
    linarith

  theorem thm32.auto : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
    have hnle : ¬ ((1 : ℝ) ≤ 0) := by linarith
    auto [hnle, le_refl] d[Monotone]

  theorem thm33 (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
    apply le_of_not_gt
    intro h'
    linarith [h _ h']

  theorem thm33.auto (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
    auto [le_of_not_gt, lt_irrefl, *]

  end

  section
  variable {α : Type*} (P : α → Prop) (Q : Prop)

  theorem thm34 (h : ¬∃ x, P x) : ∀ x, ¬P x := by
    intro x Px
    apply h
    use x

  theorem thm34.auto (h : ¬∃ x, P x) : ∀ x, ¬P x := by
    auto

  theorem thm35 (h : ∀ x, ¬P x) : ¬∃ x, P x := by
    rintro ⟨x, Px⟩
    exact h x Px

  theorem thm35.auto (h : ∀ x, ¬P x) : ¬∃ x, P x := by
    auto

  theorem thm36 (h : ∃ x, ¬P x) : ¬∀ x, P x := by
    intro h'
    rcases h with ⟨x, nPx⟩
    apply nPx
    apply h'

  theorem thm36.auto (h : ∃ x, ¬P x) : ¬∀ x, P x := by
    auto

  theorem thm37 (h : ¬∀ x, P x) : ∃ x, ¬P x := by
    by_contra h'
    apply h
    intro x
    show P x
    by_contra h''
    exact h' ⟨x, h''⟩

  theorem thm37.auto (h : ¬∀ x, P x) : ∃ x, ¬P x := by
    auto

  theorem thm38 (h : ¬¬Q) : Q := by
    by_contra h'
    exact h h'

  theorem thm38.auto (h : ¬¬Q) : Q := by
    auto

  theorem thm39 (h : Q) : ¬¬Q := by
    intro h'
    exact h' h

  theorem thm39.auto (h : Q) : ¬¬Q := by
    auto

  end

  section
  variable (f : ℝ → ℝ)

  theorem thm40 (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
    push_neg at h
    exact h

  theorem thm40.auto (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
    auto [le_of_not_gt, *] d[FnHasUb, FnUb]

  theorem thm41 (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
    dsimp only [FnHasUb, FnUb] at h
    push_neg at h
    exact h

  theorem thm41.auto (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
    auto [le_of_not_gt, *] d[FnHasUb, FnUb]

  theorem thm42 (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
    rw [Monotone] at h
    push_neg at h
    exact h

  theorem thm42.auto (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
    auto [le_of_not_gt, h] d[Monotone]

  theorem thm43 (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
    contrapose! h
    use x / 2
    constructor <;> linarith

  theorem thm43.auto (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := autoFailSorry _

  theorem thm44 (h : 0 < 0) : a > 37 :=
    absurd h (lt_irrefl 0)

  theorem thm44.auto (h : 0 < 0) : a > 37 := by
    auto [lt_irrefl, h]

  end

  theorem thm45 {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
    ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

  theorem thm45.auto {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
    auto

  theorem thm46 {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
    rcases h with ⟨h₀, h₁⟩
    contrapose! h₁
    exact le_antisymm h₀ h₁

  theorem thm46.auto {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
    auto [le_antisymm, *]

  theorem thm47 {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
    have ⟨h₀, h₁⟩ := h
    contrapose! h₁
    exact le_antisymm h₀ h₁

  theorem thm47.auto {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
    auto [le_antisymm, *]

  theorem thm48 {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
    fun h' ↦ h.right (le_antisymm h.left h')

  theorem thm48.auto {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
    auto [le_antisymm, *]

  theorem thm49 {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
    rcases h with ⟨h0, h1⟩
    constructor
    · exact h0
    intro h2
    apply h1
    apply Nat.dvd_antisymm h0 h2

  theorem thm49.auto {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
    auto [Nat.dvd_antisymm, *]

  theorem thm50 : ∃ x : ℝ, 2 < x ∧ x < 4 :=
    ⟨5 / 2, by norm_num, by norm_num⟩

  theorem thm50.auto : ∃ x : ℝ, 2 < x ∧ x < 4 := autoFailSorry _

  theorem thm51 (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
    fun ⟨z, xltz, zlty⟩ ↦ lt_trans xltz zlty

  theorem thm51.auto (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
    auto [lt_trans, *]

  theorem thm52 : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
    use 5
    use 7
    norm_num

  set_option auto.smt true in
  theorem thm52.auto : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
    auto [Nat.prime_def_lt, Nat.dvd_def]

  theorem thm53 {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
    rintro ⟨h₀, h₁⟩
    use h₀
    exact fun h' ↦ h₁ (le_antisymm h₀ h')

  theorem thm53.auto {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
    auto [le_antisymm]

  theorem thm54 {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
    constructor
    · contrapose!
      rintro rfl
      rfl
    contrapose!
    exact le_antisymm h

  theorem thm54.auto {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
    auto [le_antisymm, h]

  theorem thm55 {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
    constructor
    · rintro ⟨h0, h1⟩
      constructor
      · exact h0
      intro h2
      apply h1
      rw [h2]
    rintro ⟨h0, h1⟩
    constructor
    · exact h0
    intro h2
    apply h1
    apply le_antisymm h0 h2

  theorem thm55.auto {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
    auto [le_antisymm]

  theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
    have h' : x ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
    pow_eq_zero h'

  theorem aux.auto {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 := autoFailSorry _

  theorem thm56 (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
    constructor
    · intro h
      constructor
      · exact aux h
      rw [add_comm] at h
      exact aux h
    rintro ⟨rfl, rfl⟩
    norm_num

  theorem thm56.auto (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
    have zero_eq : (0 : ℝ) ^ 2 + 0 ^ 2 = 0 := by norm_num
    auto [add_comm, aux, zero_eq]

  section

  theorem thm57 (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
    rw [abs_lt]
    intro h
    constructor <;> linarith

  theorem thm57.auto (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := autoFailSorry _

  theorem thm58 : 3 ∣ Nat.gcd 6 15 := by
    rw [Nat.dvd_gcd_iff]
    constructor <;> norm_num

  set_option auto.smt true in
  theorem thm58.auto : 3 ∣ Nat.gcd 6 15 := by
    rw [Nat.dvd_gcd_iff]
    auto [Nat.dvd_def]

  end

  theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
    rw [Monotone]
    push_neg
    rfl

  theorem not_monotone_iff.auto {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
    auto [not_lt_of_ge, le_of_not_gt] d[Monotone]

  theorem thm59 : ¬Monotone fun x : ℝ ↦ -x := by
    rw [not_monotone_iff]
    use 0, 1
    norm_num

  theorem thm59.auto : ¬Monotone fun x : ℝ ↦ -x := by
    have h : (0 : ℝ) ≤ 1 ∧ -(0 : ℝ) > -1 := by norm_num
    auto [not_monotone_iff, h]

  section
  variable {α : Type*} [PartialOrder α]
  variable (a b : α)

  theorem thm60 : a < b ↔ a ≤ b ∧ a ≠ b := by
    rw [lt_iff_le_not_le]
    constructor
    · rintro ⟨h0, h1⟩
      constructor
      · exact h0
      intro h2
      apply h1
      rw [h2]
    rintro ⟨h0, h1⟩
    constructor
    · exact h0
    intro h2
    apply h1
    apply le_antisymm h0 h2

  theorem thm60.auto : a < b ↔ a ≤ b ∧ a ≠ b := by
    auto [lt_iff_le_not_le, le_antisymm]

  end

  section
  variable {α : Type*} [Preorder α]
  variable (a b c : α)

  theorem thm61 : ¬a < a := by
    rw [lt_iff_le_not_le]
    rintro ⟨h0, h1⟩
    exact h1 h0

  theorem thm61.auto : ¬a < a := by
    auto [lt_iff_le_not_le]

  theorem thm62 : a < b → b < c → a < c := by
    simp only [lt_iff_le_not_le]
    rintro ⟨h0, h1⟩ ⟨h2, h3⟩
    constructor
    · apply le_trans h0 h2
    intro h4
    apply h1
    apply le_trans h2 h4

  theorem thm62.auto : a < b → b < c → a < c := by
    auto [le_trans, lt_iff_le_not_le]

  end

  section

  variable {x y : ℝ}

  theorem thm63 (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
    left
    linarith [pow_two_nonneg x]

  theorem thm63.auto (h : y > x ^ 2) : y > 0 ∨ y < -1 := autoFailSorry _

  theorem thm64 (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
    right
    linarith [pow_two_nonneg x]

  theorem thm64.auto (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := autoFailSorry _

  theorem thm65 (h : y > 0) : y > 0 ∨ y < -1 :=
    Or.inl h

  theorem thm65.auto (h : y > 0) : y > 0 ∨ y < -1 := by
    auto

  theorem thm66 (h : y < -1) : y > 0 ∨ y < -1 :=
    Or.inr h

  theorem thm66.auto (h : y < -1) : y > 0 ∨ y < -1 := by
    auto

  theorem thm67 : x < |y| → x < y ∨ x < -y := by
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h]
      intro h; left; exact h
    . rw [abs_of_neg h]
      intro h; right; exact h

  theorem thm67.auto : x < |y| → x < y ∨ x < -y := by
    auto [abs_of_nonneg, abs_of_neg, le_or_gt]

  namespace MyAbs

  theorem le_abs_self (x : ℝ) : x ≤ |x| := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
    . rw [abs_of_neg h]
      linarith

  theorem le_abs_self.auto (x : ℝ) : x ≤ |x| := by
    have h : 0 > x → x ≤ -x := by intros; linarith
    auto [le_or_gt, le_refl, abs_of_nonneg, abs_of_neg, h]

  theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
      linarith
    . rw [abs_of_neg h]

  theorem neg_le_abs_self.auto (x : ℝ) : -x ≤ |x| := by
    have h : 0 ≤ x → -x ≤ x := by intros; linarith
    auto [le_or_gt, le_refl, abs_of_nonneg, abs_of_neg, h]

  theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
    rcases le_or_gt 0 (x + y) with h | h
    · rw [abs_of_nonneg h]
      linarith [le_abs_self x, le_abs_self y]
    . rw [abs_of_neg h]
      linarith [neg_le_abs_self x, neg_le_abs_self y]

  theorem abs_add.auto (x y : ℝ) : |x + y| ≤ |x| + |y| := by
    auto [add_le_add, neg_add, le_or_gt, le_abs_self, neg_le_abs_self,
          abs_of_neg, abs_of_nonneg]

  theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h]
      constructor
      · intro h'
        left
        exact h'
      . intro h'
        rcases h' with h' | h'
        · exact h'
        . linarith
    rw [abs_of_neg h]
    constructor
    · intro h'
      right
      exact h'
    . intro h'
      rcases h' with h' | h'
      · linarith
      . exact h'

  theorem lt_abs.auto : x < |y| ↔ x < y ∨ x < -y := by
    have h₁ : 0 ≤ y → x < -y → x < y := by intros; linarith
    have h₂ : 0 > y → x < y → x < -y := by intros; linarith
    auto [le_or_gt, abs_of_neg, abs_of_nonneg, *]

  theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
      constructor
      · intro h'
        constructor
        · linarith
        exact h'
      . intro h'
        rcases h' with ⟨h1, h2⟩
        exact h2
    . rw [abs_of_neg h]
      constructor
      · intro h'
        constructor
        · linarith
        . linarith
      . intro h'
        linarith

  theorem abs_lt.auto : |x| < y ↔ -y < x ∧ x < y := autoFailSorry _

  end MyAbs

  end

  theorem thm68 {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
    rcases lt_trichotomy x 0 with xlt | xeq | xgt
    · left
      exact xlt
    · contradiction
    . right; exact xgt

  theorem thm68.auto {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
    auto [lt_trichotomy, h]

  theorem thm69 {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
    rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · rw [mul_assoc]
      apply dvd_mul_right
    . rw [mul_comm, mul_assoc]
      apply dvd_mul_right

  theorem thm69.auto {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
    auto [Nat.dvd_def, mul_assoc, mul_comm, h]

  theorem thm70 {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
    rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

  theorem thm70.auto {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
    auto [show (1 : ℝ) ≥ 0 by linarith, sq_nonneg, le_refl, add_le_add, add_zero, h]

  theorem thm71 {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
    have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
    have h'' : (x + 1) * (x - 1) = 0 := by
      rw [← h']
      ring
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
    · right
      exact eq_neg_iff_add_eq_zero.mpr h1
    . left
      exact eq_of_sub_eq_zero h1

  theorem thm71.auto {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
    have h' : (x + 1) * (x - 1) = x ^ 2 - 1 := by ring
    auto [sub_self, eq_zero_or_eq_zero_of_mul_eq_zero,
          eq_neg_iff_add_eq_zero, eq_of_sub_eq_zero, h, h']

  theorem thm72 {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
    have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
    have h'' : (x + y) * (x - y) = 0 := by
      rw [← h']
      ring
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
    · right
      exact eq_neg_iff_add_eq_zero.mpr h1
    . left
      exact eq_of_sub_eq_zero h1

  theorem thm72.auto {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
    have h' : (x + y) * (x - y) = x ^ 2 - y ^ 2 := by ring
    auto [sub_self, eq_zero_or_eq_zero_of_mul_eq_zero,
          eq_neg_iff_add_eq_zero, eq_of_sub_eq_zero, h, h']

  theorem thm73 (P : Prop) : ¬¬P → P := by
    intro h
    cases em P
    · assumption
    . contradiction

  theorem thm73.auto (P : Prop) : ¬¬P → P := by
    auto

  theorem thm74 (P : Prop) : ¬¬P → P := by
    intro h
    by_cases h' : P
    · assumption
    contradiction

  theorem thm74.auto (P : Prop) : ¬¬P → P := by
    auto

  theorem thm75 (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
    constructor
    · intro h
      by_cases h' : P
      · right
        exact h h'
      . left
        exact h'
    rintro (h | h)
    · intro h'
      exact absurd h' h
    . intro
      exact h

  theorem thm75.auto (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
    auto

  def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
    ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

  theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
    intro ε εpos
    use 0
    intro n nge
    rw [sub_self, abs_zero]
    apply εpos

  theorem convergesTo_const.auto (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
    auto [sub_self, abs_zero] d[ConvergesTo]

  theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
        (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
      ConvergesTo (fun n ↦ s n + t n) (a + b) := by
    intro ε εpos
    dsimp -- this line is not needed but cleans up the goal a bit.
    have ε2pos : 0 < ε / 2 := by linarith
    rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
    rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
    use max Ns Nt
    intro n hn
    have ngeNs : n ≥ Ns := le_of_max_le_left hn
    have ngeNt : n ≥ Nt := le_of_max_le_right hn
    calc
      |s n + t n - (a + b)| = |s n - a + (t n - b)| := by
        congr
        ring
      _ ≤ |s n - a| + |t n - b| := (abs_add _ _)
      _ < ε / 2 + ε / 2 := (add_lt_add (hs n ngeNs) (ht n ngeNt))
      _ = ε := by norm_num

  theorem convergesTo_add.auto {s t : ℕ → ℝ} {a b : ℝ}
        (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
      ConvergesTo (fun n ↦ s n + t n) (a + b) := by
    have ε2pos (ε : ℝ) : 0 < ε → 0 < ε / 2 := by intros; linarith
    have halfadd (ε : ℝ) : ε / 2 + ε / 2 = ε := by linarith
    -- auto [le_of_max_le_left, le_of_max_le_right, add_sub_add_comm,
    --       lt_of_le_of_lt, abs_add, add_lt_add, *]
    exact autoFailSorry _

  theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
      ConvergesTo (fun n ↦ c * s n) (c * a) := by
    by_cases h : c = 0
    · convert convergesTo_const 0
      · rw [h]
        ring
      rw [h]
      ring
    have acpos : 0 < |c| := abs_pos.mpr h
    intro ε εpos
    dsimp
    have εcpos : 0 < ε / |c| := by apply div_pos εpos acpos
    rcases cs (ε / |c|) εcpos with ⟨Ns, hs⟩
    use Ns
    intro n ngt
    calc
      |c * s n - c * a| = |c| * |s n - a| := by rw [← abs_mul, mul_sub]
      _ < |c| * (ε / |c|) := (mul_lt_mul_of_pos_left (hs n ngt) acpos)
      _ = ε := by rw [mul_comm]; apply div_mul_cancel _ (ne_of_lt acpos).symm

  theorem convergesTo_mul_const.auto {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
      ConvergesTo (fun n ↦ c * s n) (c * a) := autoFailSorry _

  theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
      ∃ N b, ∀ n, N ≤ n → |s n| < b := by
    rcases cs 1 zero_lt_one with ⟨N, h⟩
    use N, |a| + 1
    intro n ngt
    calc
      |s n| = |s n - a + a| := by
        congr
        abel
      _ ≤ |s n - a| + |a| := (abs_add _ _)
      _ < |a| + 1 := by linarith [h n ngt]

  theorem exists_abs_le_of_convergesTo.auto {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := autoFailSorry _

  theorem aux1 {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
      ConvergesTo (fun n ↦ s n * t n) 0 := by
    intro ε εpos
    dsimp
    rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
    have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
    have pos₀ : ε / B > 0 := div_pos εpos Bpos
    rcases ct _ pos₀ with ⟨N₁, h₁⟩
    use max N₀ N₁
    intro n ngt
    have ngeN₀ : n ≥ N₀ := le_of_max_le_left ngt
    have ngeN₁ : n ≥ N₁ := le_of_max_le_right ngt
    calc
      |s n * t n - 0| = |s n| * |t n - 0| := by rw [sub_zero, abs_mul, sub_zero]
      _ < B * (ε / B) := (mul_lt_mul'' (h₀ n ngeN₀) (h₁ n ngeN₁) (abs_nonneg _) (abs_nonneg _))
      _ = ε := by rw [mul_comm]; apply div_mul_cancel _ (ne_of_lt Bpos).symm

  theorem aux1.auto {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
      ConvergesTo (fun n ↦ s n * t n) 0 := autoFailSorry _

  theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
        (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
      ConvergesTo (fun n ↦ s n * t n) (a * b) := by
    have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
      apply aux1 cs
      convert convergesTo_add ct (convergesTo_const (-b))
      ring
    have := convergesTo_add h₁ (convergesTo_mul_const b cs)
    convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
    · ext; ring
    ring

  theorem convergesTo_mul.auto {s t : ℕ → ℝ} {a b : ℝ}
        (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
      ConvergesTo (fun n ↦ s n * t n) (a * b) := autoFailSorry _

  theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
        (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
      a = b := by
    by_contra abne
    have : |a - b| > 0 := by
      apply lt_of_le_of_ne
      · apply abs_nonneg
      intro h''
      apply abne
      apply eq_of_abs_sub_eq_zero h''.symm
    let ε := |a - b| / 2
    have εpos : ε > 0 := by
      change |a - b| / 2 > 0
      linarith
    rcases sa ε εpos with ⟨Na, hNa⟩
    rcases sb ε εpos with ⟨Nb, hNb⟩
    let N := max Na Nb
    have absa : |s N - a| < ε := by
      apply hNa
      apply le_max_left
    have absb : |s N - b| < ε := by
      apply hNb
      apply le_max_right
    have : |a - b| < |a - b|
    calc
      |a - b| = |(-(s N - a)) + (s N - b)| := by
        congr
        ring
      _ ≤ |(-(s N - a))| + |s N - b| := (abs_add _ _)
      _ = |s N - a| + |s N - b| := by rw [abs_neg]
      _ < ε + ε := (add_lt_add absa absb)
      _ = |a - b| := by norm_num [ε]
    exact lt_irrefl _ this

  theorem convergesTo_unique.auto {s : ℕ → ℝ} {a b : ℝ}
        (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
      a  = b := autoFailSorry _

end Logic


namespace SetAndFunction

  section
  variable {α : Type*}
  variable (s t u : Set α)
  open Set

  theorem thm1 (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
    intro x xsu
    exact ⟨h xsu.1, xsu.2⟩

  theorem thm1.auto (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
    auto [mem_inter_iff, subset_def, h]

  theorem thm2 : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
    intro x hx
    have xs : x ∈ s := hx.1
    have xtu : x ∈ t ∪ u := hx.2
    rcases xtu with xt | xu
    · left
      show x ∈ s ∩ t
      exact ⟨xs, xt⟩
    . right
      show x ∈ s ∩ u
      exact ⟨xs, xu⟩

  set_option auto.smt true in
  theorem thm2.auto : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
    auto [mem_inter_iff, mem_union, subset_def]

  theorem thm3 : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
    rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
    · use xs; left; exact xt
    . use xs; right; exact xu

  set_option auto.smt true in
  theorem thm3.auto : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
    auto [mem_inter_iff, mem_union, subset_def]

  theorem thm4 : (s \ t) \ u ⊆ s \ (t ∪ u) := by
    intro x xstu
    have xs : x ∈ s := xstu.1.1
    have xnt : x ∉ t := xstu.1.2
    have xnu : x ∉ u := xstu.2
    constructor
    · exact xs
    intro xtu
    -- x ∈ t ∨ x ∈ u
    rcases xtu with xt | xu
    · show False; exact xnt xt
    . show False; exact xnu xu

  theorem thm4.auto : (s \ t) \ u ⊆ s \ (t ∪ u) := by
    auto [mem_diff, mem_union, subset_def]

  theorem thm5 : s \ (t ∪ u) ⊆ (s \ t) \ u := by
    rintro x ⟨xs, xntu⟩
    constructor
    use xs
    · intro xt
      exact xntu (Or.inl xt)
    intro xu
    apply xntu (Or.inr xu)

  theorem thm5.auto : s \ (t ∪ u) ⊆ (s \ t) \ u := by
    auto [mem_diff, mem_union, subset_def]

  theorem thm6 : s ∩ t = t ∩ s :=
    Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

  set_option auto.smt true in
  theorem thm6.auto : s ∩ t = t ∩ s := by
    auto [Set.ext, mem_inter_iff]

  theorem thm7 : s ∩ (s ∪ t) = s := by
    ext x; constructor
    · rintro ⟨xs, _⟩
      exact xs
    . intro xs
      use xs; left; exact xs

  set_option auto.smt true in
  theorem thm7.auto : s ∩ (s ∪ t) = s := by
    auto [Set.ext, mem_union, mem_inter_iff]

  theorem thm8 : s ∪ s ∩ t = s := by
    ext x; constructor
    · rintro (xs | ⟨xs, xt⟩) <;> exact xs
    . intro xs; left; exact xs

  set_option auto.smt true in
  theorem thm8.auto : s ∪ s ∩ t = s := by
    auto [Set.ext, mem_union, mem_inter_iff]

  theorem thm9 : s \ t ∪ t = s ∪ t := by
    ext x; constructor
    · rintro (⟨xs, nxt⟩ | xt)
      · left
        exact xs
      . right
        exact xt
    by_cases h : x ∈ t
    · intro
      right
      exact h
    rintro (xs | xt)
    · left
      use xs
    right; exact xt

  set_option auto.smt true in
  theorem thm9.auto : s \ t ∪ t = s ∪ t := by
    auto [Set.ext, mem_union, mem_diff]

  theorem thm10 : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
    ext x; constructor
    · rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
      · constructor
        left
        exact xs
        rintro ⟨_, xt⟩
        contradiction
      . constructor
        right
        exact xt
        rintro ⟨xs, _⟩
        contradiction
    rintro ⟨xs | xt, nxst⟩
    · left
      use xs
      intro xt
      apply nxst
      constructor <;> assumption
    . right; use xt; intro xs
      apply nxst
      constructor <;> assumption

  set_option auto.smt true in
  theorem thm10.auto : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
    apply Set.ext
    auto [mem_union, mem_inter_iff, mem_diff]

  def evens : Set ℕ :=
    { n | Even n }

  def odds : Set ℕ :=
    { n | ¬Even n }

  theorem thm11 : evens ∪ odds = univ := by
    rw [evens, odds]
    ext n
    simp
    apply Classical.em

  set_option auto.redMode "all" in
  theorem thm11.auto : evens ∪ odds = univ := by
    auto

  theorem thm12 (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
    h

  set_option auto.redMode "all" in
  theorem thm12.auto (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False := by
    auto

  theorem thm13 (x : ℕ) : x ∈ (univ : Set ℕ) :=
    trivial

  set_option auto.redMode "all" in
  theorem thm13.auto (x : ℕ) : x ∈ (univ : Set ℕ) := by
    auto

  theorem thm14 : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
    intro n
    simp
    intro nprime
    rcases Nat.Prime.eq_two_or_odd nprime with h | h
    · rw [h]
      intro
      linarith
    rw [Nat.even_iff, h]
    norm_num

  theorem thm14.auto : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
    intro n
    rw [mem_inter_iff]
    have h₂ : ¬ 2 < 2 := by linarith
    auto [mem_setOf, Nat.Prime.eq_two_or_odd, Nat.even_iff, *]

  end

  section

  variable (s t : Set ℕ)

  theorem thm15 (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
    intro x xs
    constructor
    · apply h₀ x xs
    apply h₁ x xs

  theorem thm15.auto (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
    auto [*]

  theorem thm16 (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
    rcases h with ⟨x, xs, _, prime_x⟩
    use x, xs

  theorem thm16.auto (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
    auto [*]

  section
  variable (ssubt : s ⊆ t)

  theorem thm17 (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
    intro x xs
    constructor
    · apply h₀ x (ssubt xs)
    apply h₁ x (ssubt xs)

  theorem thm17.auto (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
    auto [ssubt, Set.subset_def, *]

  theorem thm18 (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
    rcases h with ⟨x, xs, _, px⟩
    use x, ssubt xs

  theorem thm18.auto (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
    auto [ssubt, Set.subset_def, *]

  end

  end

  section
  variable {α I : Type*}
  variable (A B : I → Set α)
  variable (s : Set α)

  open Set

  theorem thm19 : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
    ext x
    simp only [mem_inter_iff, mem_iUnion]
    constructor
    · rintro ⟨xs, ⟨i, xAi⟩⟩
      exact ⟨i, xAi, xs⟩
    rintro ⟨i, xAi, xs⟩
    exact ⟨xs, ⟨i, xAi⟩⟩

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm19.auto : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
    apply Set.ext;
    try auto [mem_inter_iff, mem_iUnion]
    exact tptpSuccessSorry _

  theorem thm20 : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
    ext x
    simp only [mem_inter_iff, mem_iInter]
    constructor
    · intro h
      constructor
      · intro i
        exact (h i).1
      intro i
      exact (h i).2
    rintro ⟨h1, h2⟩ i
    constructor
    · exact h1 i
    exact h2 i

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm20.auto : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
    apply Set.ext
    try auto [mem_inter_iff, mem_iInter]
    exact tptpSuccessSorry _

  theorem thm21 : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
    ext x
    simp only [mem_union, mem_iInter]
    constructor
    · rintro (xs | xI)
      · intro i
        right
        exact xs
      intro i
      left
      exact xI i
    intro h
    by_cases xs : x ∈ s
    · left
      exact xs
    right
    intro i
    cases h i
    · assumption
    contradiction

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm21.auto : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
    apply Set.ext
    try auto [mem_union, mem_iInter]
    exact tptpSuccessSorry _

  def primes : Set ℕ :=
    { x | Nat.Prime x }

  theorem thm22 : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
    ext
    rw [mem_iUnion₂]
    simp

  theorem thm22.auto : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := autoFailSorry _

  theorem thm23 : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
    intro x
    contrapose!
    simp
    apply Nat.exists_prime_and_dvd

  theorem thm23.auto : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := autoFailSorry _

  theorem thm24 : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
    apply eq_univ_of_forall
    intro x
    simp
    rcases Nat.exists_infinite_primes x with ⟨p, primep, pge⟩
    use p, pge

  theorem thm24.auto : (⋃ p ∈ primes, { x | x ≤ p }) = univ := autoFailSorry _

  end

  section

  open Set

  variable {α : Type*} (s : Set (Set α))

  theorem thm25 : ⋃₀ s = ⋃ t ∈ s, t := by
    ext x
    rw [mem_iUnion₂]
    simp

  theorem thm25.auto : ⋃₀ s = ⋃ t ∈ s, t := autoFailSorry _

  theorem thm26 : ⋂₀ s = ⋂ t ∈ s, t := by
    ext x
    rw [mem_iInter₂]
    rfl

  theorem thm26.auto : ⋂₀ s = ⋂ t ∈ s, t := autoFailSorry _

  end

  section

  variable {α β : Type*}
  variable (f : α → β)
  variable (s t : Set α)
  variable (u v : Set β)

  open Function
  open Set

  theorem thm27 : f '' (s ∪ t) = f '' s ∪ f '' t := by
    ext y; constructor
    · rintro ⟨x, xs | xt, rfl⟩
      · left
        use x, xs
      right
      use x, xt
    rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
    · use x, Or.inl xs
    use x, Or.inr xt

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm27.auto : f '' (s ∪ t) = f '' s ∪ f '' t := by
    apply Set.ext
    try auto [mem_image, mem_union]
    exact tptpSuccessSorry _

  theorem thm28 : s ⊆ f ⁻¹' (f '' s) := by
    intro x xs
    show f x ∈ f '' s
    use x, xs

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm28.auto : s ⊆ f ⁻¹' (f '' s) := by
    try auto [subset_def, mem_image, mem_preimage]
    exact tptpSuccessSorry _

  theorem thm29 : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
    constructor
    · intro h x xs
      have : f x ∈ f '' s := mem_image_of_mem _ xs
      exact h this
    intro h y ymem
    rcases ymem with ⟨x, xs, fxeq⟩
    rw [← fxeq]
    apply h xs

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm29.auto : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
    try auto [subset_def, mem_image, mem_preimage]
    exact tptpSuccessSorry _

  theorem thm30 (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
    rintro x ⟨y, ys, fxeq⟩
    rw [← h fxeq]
    exact ys

  theorem thm30.auto (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
    auto [subset_def, mem_preimage, Injective.mem_set_image, h]

  theorem thm31 : f '' (f ⁻¹' u) ⊆ u := by
    rintro y ⟨x, xmem, rfl⟩
    exact xmem

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm31.auto : f '' (f ⁻¹' u) ⊆ u := by
    try auto [subset_def, mem_image, mem_preimage]
    exact tptpSuccessSorry _

  theorem thm32 (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
    intro y yu
    rcases h y with ⟨x, fxeq⟩
    use x
    constructor
    · show f x ∈ u
      rw [fxeq]
      exact yu
    exact fxeq

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm32.auto (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
    try auto [subset_def, mem_image, mem_preimage, h] d[Surjective]
    exact tptpSuccessSorry _

  theorem thm33 (h : s ⊆ t) : f '' s ⊆ f '' t := by
    rintro y ⟨x, xs, fxeq⟩
    use x, h xs

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm33.auto (h : s ⊆ t) : f '' s ⊆ f '' t := by
    try auto [subset_def, mem_image, h]
    exact tptpSuccessSorry _

  theorem thm34 (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
    intro x; apply h

  theorem thm34.auto (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
    auto [subset_def, mem_preimage, h]

  theorem thm35 : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
    ext x; rfl

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm35.auto : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
    try ext x; auto [mem_union, mem_preimage]
    exact tptpSuccessSorry _

  theorem thm36 : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
    rintro y ⟨x, ⟨xs, xt⟩, rfl⟩
    constructor
    . use x, xs
    . use x, xt

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm36.auto : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
    try auto [mem_inter_iff, subset_def, mem_image]
    exact tptpSuccessSorry _

  theorem thm37 (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
    rintro y ⟨⟨x₁, x₁s, rfl⟩, ⟨x₂, x₂t, fx₂eq⟩⟩
    use x₁
    constructor
    . use x₁s
      rw [← h fx₂eq]
      exact x₂t
    . rfl

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm37.auto (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
    intro x
    try auto [mem_inter_iff, mem_image, h] d[Injective]
    exact tptpSuccessSorry _

  theorem thm38 : f '' s \ f '' t ⊆ f '' (s \ t) := by
    rintro y ⟨⟨x₁, x₁s, rfl⟩, h⟩
    use x₁
    constructor
    . constructor
      . exact x₁s
      . intro h'
        apply h
        use x₁, h'
    . rfl

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm38.auto : f '' s \ f '' t ⊆ f '' (s \ t) := by
    intro x
    try auto [mem_image, mem_diff]
    exact tptpSuccessSorry _

  theorem thm39 : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
    fun x ↦ id

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm39.auto : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
    intro x; try auto [mem_preimage, mem_diff]
    exact tptpSuccessSorry _

  theorem thm40 : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
    ext y; constructor
    · rintro ⟨⟨x, xs, rfl⟩, fxv⟩
      use x, ⟨xs, fxv⟩
    rintro ⟨x, ⟨⟨xs, fxv⟩, rfl⟩⟩
    exact ⟨⟨x, xs, rfl⟩, fxv⟩

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm40.auto : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
    apply Set.ext
    try auto [mem_inter_iff, mem_image, mem_preimage]
    exact tptpSuccessSorry _

  theorem thm41 : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
    rintro y ⟨x, ⟨xs, fxu⟩, rfl⟩
    exact ⟨⟨x, xs, rfl⟩, fxu⟩

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm41.auto : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
    intro x
    try auto [mem_inter_iff, mem_image, mem_preimage]
    exact tptpSuccessSorry _

  theorem thm42 : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
    rintro x ⟨xs, fxu⟩
    exact ⟨⟨x, xs, rfl⟩, fxu⟩

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm42.auto : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
    intro x
    try auto [mem_inter_iff, mem_image, mem_preimage]
    exact tptpSuccessSorry _

  theorem thm43 : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
    rintro x (xs | fxu)
    · left
      exact ⟨x, xs, rfl⟩
    right; exact fxu

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm43.auto : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
    intro x
    try auto [mem_union, mem_image, mem_preimage]
    exact tptpSuccessSorry _

  variable {I : Type*} (A : I → Set α) (B : I → Set β)

  theorem thm44 : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
    ext y; simp
    constructor
    · rintro ⟨x, ⟨i, xAi⟩, fxeq⟩
      use i, x
    rintro ⟨i, x, xAi, fxeq⟩
    exact ⟨x, ⟨i, xAi⟩, fxeq⟩

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm44.auto : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
    ext y; simp
    try auto
    exact tptpSuccessSorry _

  theorem thm45 : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
    intro y; simp
    intro x h fxeq i
    use x
    exact ⟨h i, fxeq⟩

  theorem thm45.auto : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
    intro y; simp; auto

  theorem thm46 (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
    intro y; simp
    intro h
    rcases h i with ⟨x, xAi, fxeq⟩
    use x; constructor
    · intro i'
      rcases h i' with ⟨x', x'Ai, fx'eq⟩
      have : f x = f x' := by rw [fxeq, fx'eq]
      have : x = x' := injf this
      rw [this]
      exact x'Ai
    exact fxeq

  theorem thm46.auto (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
    intro y; simp; auto [injf] d[Injective]

  theorem thm47 : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
    ext x
    simp

  theorem thm47.auto : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := autoFailSorry _

  theorem thm48 : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
    ext x
    simp

  theorem thm48.auto : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := autoFailSorry _

  end

  section

  open Set Real

  theorem thm49 : InjOn log { x | x > 0 } := by
    intro x xpos y ypos
    intro e
    -- log x = log y
    calc
      x = exp (log x) := by rw [exp_log xpos]
      _ = exp (log y) := by rw [e]
      _ = y := by rw [exp_log ypos]

  theorem thm49.auto : InjOn log { x | x > 0 } := by
    intro x xpos y ypos; dsimp at *
    auto [exp_log, *]

  theorem thm50 : range exp = { y | y > 0 } := by
    ext y; constructor
    · rintro ⟨x, rfl⟩
      apply exp_pos
    intro ypos
    use log y
    rw [exp_log ypos]

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm50.auto : range exp = { y | y > 0 } := by
    ext y
    try auto [exp_pos, exp_log, mem_setOf] d[range]
    exact tptpSuccessSorry _

  theorem thm51 : InjOn sqrt { x | x ≥ 0 } := by
    intro x xnonneg y ynonneg
    intro e
    calc
      x = sqrt x ^ 2 := by rw [sq_sqrt xnonneg]
      _ = sqrt y ^ 2 := by rw [e]
      _ = y := by rw [sq_sqrt ynonneg]

  theorem thm51.auto : InjOn sqrt { x | x ≥ 0 } := by
    intro x xnonneg y ynonneg; dsimp at *
    auto [xnonneg, ynonneg, sq_sqrt]

  theorem thm52 : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
    intro x xnonneg y ynonneg
    intro e
    dsimp at *
    calc
      x = sqrt (x ^ 2) := by rw [sqrt_sq xnonneg]
      _ = sqrt (y ^ 2) := by rw [e]
      _ = y := by rw [sqrt_sq ynonneg]

  theorem thm52.auto : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
    intro x xnonneg y ynonneg; dsimp at *
    auto [xnonneg, ynonneg, sqrt_sq]

  theorem thm53 : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
    ext y; constructor
    · rintro ⟨x, ⟨xnonneg, rfl⟩⟩
      apply sqrt_nonneg
    intro ynonneg
    use y ^ 2
    dsimp at *
    constructor
    apply pow_nonneg ynonneg
    apply sqrt_sq
    assumption

  theorem thm53.auto : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
    ext y; rw [mem_image]; dsimp
    auto [sqrt_sq, sqrt_nonneg, pow_nonneg]

  theorem thm54 : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      dsimp at *
      apply pow_two_nonneg
    intro ynonneg
    use sqrt y
    exact sq_sqrt ynonneg

  theorem thm54.auto : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
    ext y; rw [mem_range]; dsimp
    auto [pow_two_nonneg, sq_sqrt]

  end

  section
  variable {α β : Type*} [Inhabited α]

  variable (P : α → Prop) (h : ∃ x, P x)

  noncomputable section

  open Classical

  def inverse (f : α → β) : β → α := fun y : β ↦
    if h : ∃ x, f x = y then Classical.choose h else default

  theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
    rw [inverse, dif_pos h]
    exact Classical.choose_spec h

  theorem inverse_spec.auto {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := autoFailSorry _

  variable (f : α → β)

  open Function

  theorem thm55 : Injective f ↔ LeftInverse (inverse f) f := by
    constructor
    · intro h y
      apply h
      apply inverse_spec
      use y
    intro h x1 x2 e
    rw [← h x1, ← h x2, e]

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm55.auto : Injective f ↔ LeftInverse (inverse f) f := by
    dsimp [Injective, LeftInverse]
    try auto [inverse_spec]
    exact tptpSuccessSorry _

  theorem thm56 : Surjective f ↔ RightInverse (inverse f) f := by
    constructor
    · intro h y
      apply inverse_spec
      apply h
    intro h y
    use inverse f y
    apply h

  set_option auto.tptp true in
  set_option auto.native false in
  theorem thm56.auto : Surjective f ↔ RightInverse (inverse f) f := by
    dsimp [Surjective, Function.RightInverse, LeftInverse]
    try auto [inverse_spec]
    exact tptpSuccessSorry _

  end

  section
  variable {α : Type*}
  open Function

  theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
    intro f surjf
    let S := { i | i ∉ f i }
    rcases surjf S with ⟨j, h⟩
    have h₁ : j ∉ f j := by
      intro h'
      have : j ∉ f j := by rwa [h] at h'
      contradiction
    have h₂ : j ∈ S := h₁
    have h₃ : j ∉ S := by rwa [h] at h₁
    contradiction

  theorem Cantor.auto : ∀ f : α → Set α, ¬Surjective f := by
    intro f surjf
    let S := { i | i ∉ f i }
    have s_spec : ∀ i, i ∈ S ↔ i ∉ f i := by intros; rfl
    auto [surjf S, s_spec]

  end

  end

  noncomputable section

  open Classical Set Function
  variable {α β : Type*} [Nonempty β]
  variable (f : α → β) (g : β → α)

  def sbAux : ℕ → Set α
    | 0 => univ \ g '' univ
    | n + 1 => g '' (f '' sbAux n)

  def sbSet :=
    ⋃ n, sbAux f g n

  def sbFun (x : α) : β :=
    if x ∈ sbSet f g then f x else invFun g x

  theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
    have : x ∈ g '' univ := by
      contrapose! hx
      rw [sbSet, mem_iUnion]
      use 0
      rw [sbAux, mem_diff]
      exact ⟨mem_univ _, hx⟩
    have : ∃ y, g y = x := by
      simp at this
      assumption
    exact invFun_eq this

  theorem sb_right_inv.auto {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := autoFailSorry _

  theorem sb_injective (hf : Injective f) : Injective (sbFun f g) := by
    set A := sbSet f g with A_def
    set h := sbFun f g with h_def
    intro x₁ x₂
    intro (hxeq : h x₁ = h x₂)
    show x₁ = x₂
    simp only [h_def, sbFun, ← A_def] at hxeq
    by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
    · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
      · symm
        apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
      have x₂A : x₂ ∈ A := by
        apply _root_.not_imp_self.mp
        intro (x₂nA : x₂ ∉ A)
        rw [if_pos x₁A, if_neg x₂nA] at hxeq
        rw [A_def, sbSet, mem_iUnion] at x₁A
        have x₂eq : x₂ = g (f x₁) := by
          rw [hxeq, sb_right_inv f g x₂nA]
        rcases x₁A with ⟨n, hn⟩
        rw [A_def, sbSet, mem_iUnion]
        use n + 1
        simp [sbAux]
        exact ⟨x₁, hn, x₂eq.symm⟩
      rw [if_pos x₁A, if_pos x₂A] at hxeq
      exact hf hxeq
    push_neg  at xA
    rw [if_neg xA.1, if_neg xA.2] at hxeq
    rw [← sb_right_inv f g xA.1, hxeq, sb_right_inv f g xA.2]

  theorem sb_injective.auto (hf : Injective f) : Injective (sbFun f g) := autoFailSorry _

  theorem sb_surjective (hf : Injective f) (hg : Injective g) : Surjective (sbFun f g) := by
    set A := sbSet f g with A_def
    set h := sbFun f g with h_def
    intro y
    by_cases gyA : g y ∈ A
    · rw [A_def, sbSet, mem_iUnion] at gyA
      rcases gyA with ⟨n, hn⟩
      rcases n with _ | n
      · simp [sbAux] at hn
      simp [sbAux] at hn
      rcases hn with ⟨x, xmem, hx⟩
      use x
      have : x ∈ A := by
        rw [A_def, sbSet, mem_iUnion]
        exact ⟨n, xmem⟩
      simp only [h_def, sbFun, if_pos this]
      exact hg hx
    use g y
    simp only [h_def, sbFun, if_neg gyA]
    apply leftInverse_invFun hg

    theorem sb_surjective.auto (hf : Injective f) (hg : Injective g) : Surjective (sbFun f g) := autoFailSorry _

  end

end SetAndFunction
