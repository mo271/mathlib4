/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.RingTheory.Derivation.Higher

/-!
# Polynomial Hasse Derivatives as Higher Derivations

This file bundles `Polynomial.hasseDeriv` into a `HigherDerivation`,
showing that the Hasse derivatives of polynomials form a
Hasse-Schmidt derivation.

## Main definitions

* `Polynomial.hasseDerivHigherDerivation`: The Hasse derivatives of
  polynomials, bundled as a `HigherDerivation R R[X]`.
-/

@[expose] public section

open Finset Finset.Nat

namespace Polynomial

variable {R : Type*} [Semiring R]

/-- The Hasse derivatives of polynomials form a higher derivation.
This bundles `Polynomial.hasseDeriv` into a `HigherDerivation`. -/
noncomputable def hasseDerivHigherDerivation :
    HigherDerivation R R[X] where
  toLinearMap k := hasseDeriv k
  map_zero' := hasseDeriv_zero
  map_one' k hk := hasseDeriv_apply_one k hk
  leibniz' k f g := hasseDeriv_mul k f g

@[simp]
theorem hasseDerivHigherDerivation_apply (k : ℕ) :
    (hasseDerivHigherDerivation :
      HigherDerivation R R[X]) k = hasseDeriv k :=
  rfl

end Polynomial
