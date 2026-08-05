/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Higher Derivations (Hasse-Schmidt Derivations)

A higher derivation on a module `A` over a semiring `R` is a
sequence of `R`-linear maps `D : ℕ → (A →ₗ[R] A)` satisfying:
1. `D 0 = LinearMap.id`
2. `D n 1 = 0` for `n > 0`
3. The divided Leibniz rule:
   `D n (a * b) = ∑ ij ∈ antidiagonal n, D ij.1 a * D ij.2 b`

Higher derivations were introduced by Hasse and Schmidt to provide a correct notion of
iterated differentiation in positive characteristic, where the usual iterated derivative
`d^k/dx^k` vanishes for `k ≥ p`.

## Main definitions

* `HigherDerivation R A`: The type of higher derivations from `A` to `A` over `R`.
* `HigherDerivation.toDerivation`: The first component `D 1` is an ordinary `Derivation R A A`
  (requires `Algebra R A`).
* `HigherDerivation.mk'`: Constructor that deduces `map_one` from the Leibniz rule when `A` is a
  ring (where additive cancellation is available).

## References

* <https://math.fontein.de/2009/08/12/the-hasse-derivative/>
-/

@[expose] public section

open Finset Finset.HasAntidiagonal

/-- A `HigherDerivation R A` is a sequence `D : ℕ → (A →ₗ[R] A)` of `R`-linear maps
satisfying `D 0 = id`, `D n 1 = 0` for `n > 0`, and the divided Leibniz rule
`D n (a * b) = ∑ ij ∈ antidiagonal n, D ij.1 a * D ij.2 b`.

This is also known as a Hasse-Schmidt derivation. -/
structure HigherDerivation (R : Type*) (A : Type*) [Semiring R] [Semiring A]
    [Module R A] where
  /-- The family of `R`-linear maps. -/
  toLinearMap : ℕ → (A →ₗ[R] A)
  /-- The zeroth component is the identity. -/
  protected map_zero' : toLinearMap 0 = LinearMap.id
  /-- The image of `1` under each higher component is `0`. -/
  protected map_one' (n : ℕ) (hn : 0 < n) : toLinearMap n 1 = 0
  /-- The divided Leibniz rule. -/
  protected leibniz' (n : ℕ) (a b : A) :
    toLinearMap n (a * b) = ∑ ij ∈ antidiagonal n, toLinearMap ij.1 a * toLinearMap ij.2 b

namespace HigherDerivation

section Semiring

variable {R : Type*} {A : Type*} [Semiring R] [Semiring A] [Module R A]

instance : FunLike (HigherDerivation R A) ℕ (A →ₗ[R] A) where
  coe D := D.toLinearMap
  coe_injective D₁ D₂ h := by cases D₁; cases D₂; congr

@[ext]
theorem ext {D₁ D₂ : HigherDerivation R A} (h : ∀ n, D₁ n = D₂ n) : D₁ = D₂ :=
  DFunLike.coe_injective (funext h)

variable (D : HigherDerivation R A)

@[simp]
theorem map_zero : D 0 = LinearMap.id := D.map_zero'

theorem leibniz (n : ℕ) (a b : A) :
    D n (a * b) = ∑ ij ∈ antidiagonal n, D ij.1 a * D ij.2 b :=
  D.leibniz' n a b

@[simp]
theorem map_zero_apply (a : A) : D 0 a = a := by
  rw [map_zero]; rfl

theorem map_one (n : ℕ) (hn : 0 < n) : D n 1 = 0 := D.map_one' n hn

end Semiring

section Algebra

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable (D : HigherDerivation R A)

theorem map_algebraMap (n : ℕ) (hn : 0 < n) (r : R) : D n (algebraMap R A r) = 0 := by
  have h : algebraMap R A r = r • (1 : A) := by rw [Algebra.smul_def, mul_one]
  rw [h, (D n).map_smul, map_one D n hn, smul_zero]

end Algebra

section Ring

variable {R : Type*} {A : Type*} [Semiring R] [Ring A] [Module R A]

/-- Constructor for `HigherDerivation` over a `Ring`, where the condition `D n 1 = 0`
is automatically deduced from the Leibniz rule by induction.

The proof works by strong induction: applying the Leibniz rule to `D (n+1) (1 * 1)` gives
`D (n+1) 1 = ∑_{i+j=n+1} D i 1 * D j 1`. The boundary terms `(0, n+1)` and `(n+1, 0)`
each contribute `D (n+1) 1` (using `D 0 = id`), and all interior terms vanish by the
inductive hypothesis (since `1 ≤ i ≤ n` implies `D i 1 = 0`). Thus
`D (n+1) 1 = 2 · D (n+1) 1`, giving `D (n+1) 1 = 0`. -/
def mk' (D : ℕ → (A →ₗ[R] A))
    (hD0 : D 0 = LinearMap.id)
    (hL : ∀ (n : ℕ) (a b : A),
      D n (a * b) = ∑ ij ∈ antidiagonal n, D ij.1 a * D ij.2 b) :
    HigherDerivation R A where
  toLinearMap := D
  map_zero' := hD0
  map_one' := by
    -- Strong induction: assume D m 1 = 0 for all 0 < m < n
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
    intro hn
    match n, hn with
    | n + 1, _ =>
      have h := hL (n + 1) 1 1
      simp only [mul_one] at h
      -- Simplify each summand using D 0 = id and induction
      have h_eval : ∀ ij ∈ (antidiagonal (n + 1) : Finset (ℕ × ℕ)),
          (D ij.1) 1 * (D ij.2) 1 =
            if ij.1 = 0 then (D ij.2) 1
            else if ij.2 = 0 then (D ij.1) 1
            else 0 := by
        intro ij hij
        rw [mem_antidiagonal] at hij
        split_ifs with h1 h2
        · rw [show D ij.1 = D 0 from congrArg D h1, hD0, LinearMap.id_apply, one_mul]
        · rw [show D ij.2 = D 0 from congrArg D h2, hD0, LinearMap.id_apply, mul_one]
        · rw [ih ij.1 (by omega) (Nat.pos_of_ne_zero h1), zero_mul]
      rw [Finset.sum_congr rfl h_eval] at h
      -- The filter {ij | ij.1 = 0} ∩ antidiagonal (n+1) = {(0, n+1)}
      have hf0 : ((antidiagonal (n + 1) : Finset (ℕ × ℕ)).filter (fun ij => ij.1 = 0)) =
          {(0, n + 1)} := by
        ext ij; simp only [Finset.mem_filter, mem_antidiagonal, Finset.mem_singleton]
        constructor
        · rintro ⟨hij, h1⟩; ext <;> omega
        · rintro rfl; simp
      -- The filter {ij | ij.1 ≠ 0 ∧ ij.2 = 0} ∩ antidiagonal (n+1) = {(n+1, 0)}
      have hf1 : ((antidiagonal (n + 1) : Finset (ℕ × ℕ)).filter
          (fun ij => ¬ij.1 = 0)).filter (fun ij => ij.2 = 0) = {(n + 1, 0)} := by
        ext ij; simp only [Finset.mem_filter, mem_antidiagonal, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hij, h1⟩, h2⟩; ext <;> omega
        · rintro rfl; refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp
      rw [Finset.sum_ite, Finset.sum_ite] at h
      rw [hf0, hf1, Finset.sum_singleton, Finset.sum_singleton] at h
      simp only [Finset.sum_const_zero, add_zero] at h
      -- h : D(n+1) 1 = D(n+1) 1 + D(n+1) 1, so D(n+1) 1 = 0
      have : D (n + 1) 1 + D (n + 1) 1 - D (n + 1) 1 = D (n + 1) 1 :=
        add_sub_cancel_right _ _
      rw [← h, sub_self] at this
      exact this.symm
  leibniz' := hL

end Ring

section CommRing

variable {R : Type*} {A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The first component of a higher derivation is an ordinary derivation. -/
def toDerivation (D : HigherDerivation R A) : Derivation R A A where
  toLinearMap := D 1
  map_one_eq_zero' := D.map_one 1 one_pos
  leibniz' a b := by
    have h := D.leibniz 1 a b
    have h_anti : (antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} := rfl
    rw [h_anti, Finset.sum_pair (by decide)] at h
    simp only [map_zero_apply] at h
    rw [h, smul_eq_mul, smul_eq_mul, mul_comm b _]


variable (D : Derivation R A A)

lemma derivation_pow_apply (k : ℕ) (y : A) :
    (D : A →ₗ[R] A) (((D : A →ₗ[R] A) ^ k) y) =
      ((D : A →ₗ[R] A) ^ (k + 1)) y := by
  rw [← Module.End.mul_apply, ← pow_succ']

lemma derivation_leibniz_mul (a b : A) :
    (D : A →ₗ[R] A) (a * b) =
      a * (D : A →ₗ[R] A) b + (D : A →ₗ[R] A) a * b := by
  have := D.leibniz a b
  change D (a * b) = a * D b + D a * b
  rw [this]
  simp [mul_comm]

lemma sum_antidiagonal_choose_succ_smul_cast_symm (f : ℕ → ℕ → A) (n : ℕ) :
    ∑ ij ∈ antidiagonal n, (↑(n.choose ij.1) : R) • f ij.1 (ij.2 + 1) +
    ∑ ij ∈ antidiagonal n, (↑(n.choose ij.1) : R) • f (ij.1 + 1) ij.2 =
    ∑ ij ∈ antidiagonal (n + 1), (↑((n + 1).choose ij.1) : R) • f ij.1 ij.2 := by
  have : ∑ ij ∈ antidiagonal n, (↑(n.choose ij.1) : R) • f (ij.1 + 1) ij.2 =
      ∑ ij ∈ antidiagonal n, (↑(n.choose ij.2) : R) • f (ij.1 + 1) ij.2 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [mem_antidiagonal] at hx
    have h1 : x.1 ≤ n := by omega
    have h2 : n - x.1 = x.2 := by omega
    have h3 : n.choose x.1 = n.choose x.2 := by rw [← Nat.choose_symm h1, h2]
    rw [h3]
  rw [this]
  simp_rw [Nat.cast_smul_eq_nsmul R]
  exact (sum_antidiagonal_choose_succ_nsmul f n).symm

theorem _root_.Derivation.iterate_leibniz (n : ℕ) (a b : A) :
    ((D : A →ₗ[R] A) ^ n) (a * b) =
      ∑ ij ∈ antidiagonal n, (n.choose ij.1 : R) •
        (((D : A →ₗ[R] A) ^ ij.1) a * ((D : A →ₗ[R] A) ^ ij.2) b) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp only [pow_succ']
    rw [Module.End.mul_apply, ih, map_sum]
    simp only [LinearMap.map_smul, derivation_leibniz_mul, smul_add, derivation_pow_apply]
    simp_rw [sum_add_distrib]
    exact sum_antidiagonal_choose_succ_smul_cast_symm
      (fun i j => (((D : A →ₗ[R] A) ^ i) a) * (((D : A →ₗ[R] A) ^ j) b)) n

section toHigherDerivation

variable [Algebra ℚ R]

lemma rat_choose_factorial (n i j : ℕ) (h : i + j = n) :
    (1 / (n.factorial : ℚ)) * (n.choose i : ℚ) =
      (1 / (i.factorial : ℚ)) * (1 / (j.factorial : ℚ)) := by
  have h2 : (n.choose i : ℚ) * (i.factorial : ℚ) * (j.factorial : ℚ) = (n.factorial : ℚ) := by
    have h_nat : n.choose i * i.factorial * j.factorial = n.factorial := by
      have hj : n - i = j := by omega
      have := Nat.choose_mul_factorial_mul_factorial (show i ≤ n by omega)
      rw [hj] at this
      exact this
    exact_mod_cast h_nat
  rw [← h2]
  calc
    (1 / ((n.choose i : ℚ) * (i.factorial : ℚ) * (j.factorial : ℚ))) * (n.choose i : ℚ)
      = ((n.choose i : ℚ) * 1) /
          ((n.choose i : ℚ) * ((i.factorial : ℚ) * (j.factorial : ℚ))) := by
        ring
    _ = 1 / ((i.factorial : ℚ) * (j.factorial : ℚ)) := by
      have h_nz : (n.choose i : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (show i ≤ n by omega)).ne'
      rw [mul_div_mul_left 1 _ h_nz]
    _ = (1 / (i.factorial : ℚ)) * (1 / (j.factorial : ℚ)) := by ring

/-- In characteristic zero, an ordinary derivation gives rise to a higher derivation via the
formula `D n = (1 / n.factorial) D^n`. -/
def _root_.Derivation.toHigherDerivation (D : Derivation R A A) : HigherDerivation R A :=
  HigherDerivation.mk'
    (fun n => (algebraMap ℚ R (1 / (n.factorial : ℚ)) : R) • (D : A →ₗ[R] A) ^ n)
    (by
      simp only [Nat.factorial_zero, Nat.cast_one, div_self, ne_eq, one_ne_zero,
        not_false_eq_true, pow_zero]
      rw [_root_.map_one, one_smul]
      rfl
    )
    (by
      intro n a b
      simp only [LinearMap.smul_apply]
      rw [Derivation.iterate_leibniz D n]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro ij hij
      rw [mem_antidiagonal] at hij
      have hc : (n.choose ij.1 : R) = algebraMap ℚ R (n.choose ij.1 : ℚ) :=
        _root_.map_natCast (algebraMap ℚ R) (n.choose ij.1) |>.symm
      rw [hc, ← mul_smul, ← _root_.map_mul (algebraMap ℚ R)]
      rw [rat_choose_factorial n ij.1 ij.2 hij]
      rw [_root_.map_mul, smul_mul_smul]
    )

end toHigherDerivation

end CommRing

end HigherDerivation
