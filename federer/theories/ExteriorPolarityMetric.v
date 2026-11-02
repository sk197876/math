(** Federer (1969), 1.7.5, p. 33: beta_m is an isomorphism in finite
    dimension, and the inner product on one-forms on m-vectors makes beta_m
    orthogonal. The existing sealed dual-inner-product interface supplies
    this metric. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorPositivity
  InnerExteriorPolarity InnerPolarity InnerPolaritySurjection InnerDualUP InnerDual
  LinearBasis FiniteOrdinalBasis FiniteExteriorPowers ExteriorIndices
  ExteriorGrading AlternatingCoordinates ExteriorCovectorInner
  ExteriorCovectorIdentification AlternatingIsomorphism OneFormIdentification Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Metric.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.
Local Notation P := (exterior_power V m).
Local Notation C := (@exterior_inner_form R h2 V B hB m).
Local Notation hC := (@exterior_inner_productP R h2 V B hB m).
Local Notation b := (fun i : 'I_#|{:Lambda n m}| => e_lambda e (val (enum_val i))).
Local Notation hb := (@finite_ordinal_basis R (Finite.clone (Lambda n m) _) P
  (fun lambda => e_lambda e (val lambda)) (@finite_e_lambda_basis R n V e he h2 m)).

(** Source for [exterior_polarity_inverse_exists]: Federer
    1.7.5, p. 33, beta_m has a two-sided linear inverse
    in finite dimension, including degrees above the ambient dimension. *)
Theorem exterior_polarity_inverse_exists :
  exists g : {linear A_m P R^o 1 -> P},
    cancel (@exterior_polarity R h2 V B hB m) g /\
    cancel g (@exterior_polarity R h2 V B hB m).
Proof.
have hi := @inner_polarity_injective R P C hC.
have hs := @inner_polarity_surjective R P C hC #|{:Lambda n m}| b hb.
pose g := linear_inverse hi hs.
exists (GRing.Linear.clone _ _ _ _ g _); split;
  [exact: linear_inverseKV | exact: linear_inverseK].
Qed.

(** Source for [exterior_polarity_dual_product]: Federer
    1.7.5, p. 33, the inner product on one-forms on
    m-vectors, obtained from the sealed dual-product specification. *)
Definition exterior_polarity_dual_product := @inner_dual_product R P C hC #|{:Lambda n m}| b hb.

(** Source for [exterior_polarity_dual_specification]: Federer
    1.7.5, p. 33, this is an inner product making the
    exterior polarity beta_m orthogonal. *)
Theorem exterior_polarity_dual_specification :
  is_dual_inner_product hC exterior_polarity_dual_product.
Proof. exact: inner_dual_specification. Qed.

(** Source for [exterior_polarity_isometry]: Federer 1.7.5,
    p. 33, beta_m preserves inner products for the specified
    metric on one-forms on m-vectors. *)
Theorem exterior_polarity_isometry (x y : P) :
  exterior_polarity_dual_product (@exterior_polarity R h2 V B hB m x) (@exterior_polarity R h2 V B hB m y) = C x y.
Proof. exact (@dual_inner_product_polarity R P C hC
  exterior_polarity_dual_product exterior_polarity_dual_specification x y). Qed.

(** Source for [exterior_covector_canonical_isometry]: Federer
    1.7.5, p. 33, the canonical identification of m-covectors
    with one-forms on m-vectors preserves the two induced products. *)
Theorem exterior_covector_canonical_isometry (a d : A_m V R^o m) :
  exterior_polarity_dual_product (one_form (form_to_hom a)) (one_form (form_to_hom d)) =
    exterior_covector_inner h2 hB he a d.
Proof.
exact (@exterior_covector_identification_orthogonal R h2 V B hB n e he m
  (@exterior_covector_inner R h2 V B hB n e he m) exterior_polarity_dual_product
  (exterior_covector_innerP h2 hB he m) exterior_polarity_dual_specification a d).
Qed.
End Metric.
