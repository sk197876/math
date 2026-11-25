(** Federer (1969), 4.1.7, p. 357: the
    mass/comass dual identification for the actual
    Euclidean coefficient spaces, including the prior
    degree-zero absolute-scalar correction. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP RealFunctionalNormUP
  RealFunctionalNormCongruence GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  ExteriorGrading AlternatingForms PairingLinear Comass Mass CurrentCoefficientNorms
  MultivectorDualUP MultivectorDualSealed MassFunctionalNorm ExteriorPairingFunctionalNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDualNorm.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation V := (R_n R n).
Local Notation B := (@euclidean_inner_product R n).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation e := (@coordinate_basis R n).
Local Notation he := (@coordinate_basisP R n).

(** Source for [current_mass_pairing_norm]: the actual
    vector mass is dual to the original form comass,
    Federer 4.1.7, p. 357, at every degree. *)
Theorem current_mass_pairing_norm m (xi:exterior_power V m):
  is_real_functional_norm (@current_form_comass R h2 n m)
    (pairing_right xi) (@current_vector_mass R h2 n m xi).
Proof.
case:m xi=>[xi|p xi].
- exact:(@exterior_pairing_real_functional_norm R h2 V B hB n e he 0 xi).
- exact:(@mass_is_pairing_functional_norm R h2 V B hB p.+1 (ltn0Sn p)
    (@comass R h2 V B hB n e he p.+1 (ltn0Sn p))
    (@comassP R h2 V B hB n e he p.+1 (ltn0Sn p)) xi
    (@mass R h2 V B hB n e he p.+1 (ltn0Sn p) xi)
    (@massP R h2 V B hB n e he p.+1 (ltn0Sn p) xi)).
Qed.

(** Source for [current_multivector_dual_norm]: the
    opaque canonical evaluation has exactly the mass
    norm required by Federer 4.1.7, p. 357. *)
Theorem current_multivector_dual_norm m (xi:exterior_power V m):
  is_real_functional_norm (@current_form_comass R h2 n m)
    (hom_as_linear (@MultivectorDual.evaluation R V m xi))
    (@current_vector_mass R h2 n m xi).
Proof.
apply:(@real_functional_norm_pointwise R (A_m V R^o m)
  (@current_form_comass R h2 n m) (pairing_right xi)
  (hom_as_linear (@MultivectorDual.evaluation R V m xi))
  (@current_vector_mass R h2 n m xi)).
- move=>phi; symmetry; exact:(@MultivectorDual.laws R V m xi phi).
- exact:current_mass_pairing_norm.
Qed.
End CurrentDualNorm.
