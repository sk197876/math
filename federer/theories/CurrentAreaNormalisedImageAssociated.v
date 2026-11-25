(** Federer (1969), 4.1.25, p. 383: the
    associated plane of a nonzero normalized differential
    summand is the image of the actual differential.
    Reuse the top-degree factorization of 1.7.6,
    p. 34, and the associated-space calculation of
    1.6.1, p. 24. No new tangent is chosen. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import ModuleQuotient SubspaceCarrier Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanLinearMaps ExteriorGrading ExteriorMaps ExteriorMapNormContinuity ExteriorNorm
  ExteriorFrameUnitNorm TopExteriorNorm AssociatedSubspace
  SimpleElementary EuclideanLinearJacobian EuclideanDifferentialOrientation
  PartialFunctionUP CurrentAreaNormalisedImageUP CurrentAreaNormalisedImageSealed
  FiniteCoordinates FiniteExteriorPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_area_normalised_image_associated]:
    the differential-image plane used in the last
    paragraph of Federer 4.1.25, p. 383. This is
    a law at every original defined nonzero summand,
    including degree zero; no differential is supplied
    at an undefined source point. *)
Theorem current_area_normalised_image_associated (R : realType) m n
    (f : R_n R m -> R_n R n)
    (xi : R_n R m -> exterior_power (R_n R m) m) x v :
  partial_function_graph (@CurrentAreaNormalisedImage.value R m n f xi) x v ->
  v != 0 -> exists D : Hom (R_n R m) (R_n R n),
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT f x D /\
    injective D /\ [set z | FedererSimple.T v z] = range D.
Proof.
move=> hValue hV.
have [D [hD [hJ hFormula]]] :=
  (@CurrentAreaNormalisedImage.laws R m n f xi x v).1 hValue.
have hPositive : 0 < euclidean_linear_jacobian m D.
  by rewrite lt_def hJ euclidean_linear_jacobian_nonnegative.
have hInjective := (euclidean_linear_jacobian_top_positive D).1 hPositive.
pose e := @coordinate_basis R m.
pose omega := e_lambda e (ord_tuple m).
have hOmega : omega != 0.
  by rewrite -(exterior_norm_eq0 (euclidean_two_nonzero R)
    (@euclidean_inner_productP R m))
    (@euclidean_top_product_unit_norm R (euclidean_two_nonzero R) m) oner_eq0.
have [c hXi] := @nonzero_top_vector_spans R (euclidean_two_nonzero R)
  (R_n R m) m e (@coordinate_basisP R m) omega hOmega (xi x).
have hWord : exterior_power_map (hom_as_linear D) m omega =
    euclidean_differential_top_word D.
  exact: exterior_power_map_e_lambda.
have hVector : v = ((euclidean_linear_jacobian m D)^-1*c) *:
    euclidean_differential_top_word D.
  by rewrite -hFormula /current_area_normalised_image_coefficient hXi linearZ
    hWord scalerA.
have hScalar : (euclidean_linear_jacobian m D)^-1*c != 0.
  apply/eqP => hZero; move: hV.
  by rewrite hVector hZero scale0r eqxx.
exists D; split; first exact: hD.
split; first exact: hInjective.
rewrite hVector -(@euclidean_differential_top_word_associated R m n D hInjective).
apply/seteqP; split=> z.
- exact: (@associated_scale_nonzero R (R_n R n) m
    (euclidean_differential_top_word D) _ hScalar z).1.
- exact: (@associated_scale_nonzero R (R_n R n) m
    (euclidean_differential_top_word D) _ hScalar z).2.
Qed.
