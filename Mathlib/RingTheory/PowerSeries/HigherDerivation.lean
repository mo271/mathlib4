/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.RingTheory.Derivation.Higher
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Higher Derivations and Formal Power Series

This file establishes the canonical equivalence between higher derivations (Hasse-Schmidt
derivations) on an algebra `A` and algebra homomorphisms `A →ₐ[R] A⟦X⟧` whose constant
coefficient is the identity.

## Main definitions

* `HigherDerivation.toPowerSeriesRingHom`: The ring homomorphism `A →+* A⟦X⟧` given by
  `a ↦ ∑ D_n(a) X^n`.
* `HigherDerivation.toPowerSeriesAlgHom`: The `R`-algebra homomorphism `A →ₐ[R] A⟦X⟧` given by
  `a ↦ ∑ D_n(a) X^n`.
* `HigherDerivation.ofPowerSeriesAlgHom`: The higher derivation defined from an algebra homomorphism
  `φ : A →ₐ[R] A⟦X⟧` satisfying `constantCoeff (φ a) = a`.

## Main results

* `HigherDerivation.map_pow`: The multinomial Leibniz rule for higher derivatives of powers,
  `D n (a ^ m) = coeff n (D.toPowerSeriesRingHom a ^ m)`.
* Round-trip equivalence between higher derivations and such algebra homomorphisms.
-/

@[expose] public section

open Finset Finset.HasAntidiagonal
open PowerSeries

namespace HigherDerivation

section Semiring

variable {R A : Type*} [Semiring R] [Semiring A] [Module R A]
variable (D : HigherDerivation R A)

/-- The canonical ring homomorphism `A →+* A⟦X⟧` associated to a higher derivation,
given by `a ↦ ∑ D_n(a) X^n`. -/
noncomputable def toPowerSeriesRingHom : A →+* A⟦X⟧ where
  toFun a := PowerSeries.mk (fun n => D n a)
  map_one' := by
    ext n
    rw [coeff_mk, coeff_one]
    split_ifs with hn
    · subst hn; simp
    · exact D.map_one n (Nat.pos_of_ne_zero hn)
  map_mul' a b := by
    ext n
    simp only [coeff_mk, coeff_mul, D.leibniz]
  map_zero' := by
    ext n
    simp only [coeff_mk, _root_.map_zero]
  map_add' a b := by
    ext n
    simp only [coeff_mk, map_add, _root_.map_add]

@[simp]
theorem toPowerSeriesRingHom_apply (a : A) :
    D.toPowerSeriesRingHom a = PowerSeries.mk (fun n => D n a) :=
  rfl

@[simp]
theorem coeff_toPowerSeriesRingHom (a : A) (n : ℕ) :
    coeff n (D.toPowerSeriesRingHom a) = D n a := by
  rw [toPowerSeriesRingHom_apply, coeff_mk]

theorem map_pow (a : A) (m : ℕ) (n : ℕ) :
    D n (a ^ m) = coeff n (D.toPowerSeriesRingHom a ^ m) := by
  rw [← coeff_toPowerSeriesRingHom, _root_.map_pow]

end Semiring

section CommSemiring

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
variable (D : HigherDerivation R A)

/-- The canonical algebra homomorphism `A →ₐ[R] A⟦X⟧` associated to a higher derivation,
given by `a ↦ ∑ D_n(a) X^n`. -/
noncomputable def toPowerSeriesAlgHom : A →ₐ[R] A⟦X⟧ where
  toRingHom := D.toPowerSeriesRingHom
  commutes' r := by
    ext n
    dsimp [toPowerSeriesRingHom]
    rw [coeff_mk, algebraMap_apply, coeff_C]
    split_ifs with hn
    · subst hn; simp
    · exact D.map_algebraMap n (Nat.pos_of_ne_zero hn) r

@[simp]
theorem toPowerSeriesAlgHom_apply (a : A) :
    D.toPowerSeriesAlgHom a = PowerSeries.mk (fun n => D n a) :=
  rfl

@[simp]
theorem coeff_toPowerSeriesAlgHom (a : A) (n : ℕ) :
    coeff n (D.toPowerSeriesAlgHom a) = D n a :=
  D.coeff_toPowerSeriesRingHom a n

/-- Construct a higher derivation from an algebra homomorphism `A →ₐ[R] A⟦X⟧` whose
constant term is the identity. -/
noncomputable def ofPowerSeriesAlgHom (φ : A →ₐ[R] A⟦X⟧)
    (hφ0 : ∀ a, coeff 0 (φ a) = a) : HigherDerivation R A where
  toLinearMap n :=
    { toFun := fun a => coeff n (φ a)
      map_add' := fun a b => by simp only [map_add, _root_.map_add]
      map_smul' := fun r a => by
        have : φ (r • a) = r • φ a := _root_.map_smul φ r a
        rw [this, RingHom.id_apply, ← algebraMap_smul A r (φ a),
          coeff_smul, algebraMap_smul] }
  map_zero' := LinearMap.ext hφ0
  map_one' n hn := by
    dsimp
    have : φ 1 = 1 := _root_.map_one φ
    rw [this, coeff_one, if_neg (Nat.ne_of_gt hn)]
  leibniz' n a b := by
    dsimp
    have : φ (a * b) = φ a * φ b := _root_.map_mul φ a b
    rw [this, coeff_mul]

@[simp]
theorem ofPowerSeriesAlgHom_apply (φ : A →ₐ[R] A⟦X⟧) (hφ0 : ∀ a, coeff 0 (φ a) = a)
    (n : ℕ) (a : A) :
    (ofPowerSeriesAlgHom φ hφ0) n a = coeff n (φ a) :=
  rfl

@[simp]
theorem toPowerSeriesAlgHom_ofPowerSeriesAlgHom (φ : A →ₐ[R] A⟦X⟧)
    (hφ0 : ∀ a, coeff 0 (φ a) = a) :
    (ofPowerSeriesAlgHom φ hφ0).toPowerSeriesAlgHom = φ := by
  ext a n
  simp

@[simp]
theorem ofPowerSeriesAlgHom_toPowerSeriesAlgHom :
    ofPowerSeriesAlgHom D.toPowerSeriesAlgHom (fun a => by simp) = D := by
  ext n a
  simp

end CommSemiring

section Ring

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (D : HigherDerivation R A)

/-- The image of an invertible element under `toPowerSeriesRingHom` is a unit in `A⟦X⟧`. -/
noncomputable def toPowerSeriesUnits (u : Aˣ) : (A⟦X⟧)ˣ :=
  Units.map D.toPowerSeriesRingHom.toMonoidHom u

@[simp]
theorem coe_toPowerSeriesUnits (u : Aˣ) :
    (D.toPowerSeriesUnits u : A⟦X⟧) = D.toPowerSeriesRingHom (u : A) :=
  rfl

/-- The Hasse derivative of an inverse `u⁻¹` of a unit is given by the power series inverse. -/
theorem map_inv (u : Aˣ) (n : ℕ) :
    D n (↑u⁻¹ : A) = coeff n (↑(D.toPowerSeriesUnits u)⁻¹ : A⟦X⟧) := by
  rw [← coeff_toPowerSeriesRingHom]
  have : D.toPowerSeriesRingHom (↑u⁻¹ : A) = ↑(D.toPowerSeriesUnits u)⁻¹ := by
    simp [toPowerSeriesUnits]
  rw [this]

end Ring

end HigherDerivation
