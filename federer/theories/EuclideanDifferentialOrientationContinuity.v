(** Federer (1969), 3.2.25, p. 261: Borel dependence
    of the normalized top differential word on the actual
    differential. The word is polynomial and continuous; unit
    normalization is continuous off zero and Borel everywhere. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps CoordinateProjection EuclideanCoordinateTopology InnerNorm InnerMetric
  HilbertFormCompactness InnerExterior InnerExteriorPositivity ExteriorGrading FiniteExteriorPowers
  ExteriorProductContinuity OrthonormalFamilies NormMetric EuclideanHomOperator
  ContinuousOperatorEvaluation InnerOwnNormTopology HomeomorphismUP InnerUnitNormalization
  EuclideanDifferentialOrientation BorelFunctionUP BorelFunctionBasic ContinuousBorelPreimages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ArrowAsProduct.
Local Open Scope ring_scope.

(** Source for [euclidean_operator_point_continuous]: evaluations
    of D on fixed coordinate vectors are continuous, supporting
    S in 3.2.25, p. 261. This is the abstract
    operator-norm evaluation law of 3.1.1, p. 211,
    expressed in the existing Euclidean inner-product topology. *)
Lemma euclidean_operator_point_continuous (R:realType) m n (x:R_n R m):
  continuous (fun D:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (D x:inner_metric_space (@euclidean_inner_productP R n))).
Proof.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose ev:=hom_of_linear (linear_id (Hom (R_n R m) (R_n R n))).
have hEvaluation:=@continuous_operator_evaluation_continuous R (R_n R m) (R_n R n)
  (Hom (R_n R m) (R_n R n)) NX NY hNX hNY ev (@euclidean_operator_norm R m n)
  (@euclidean_hom_operator_space R m n) x.
have hIdentity:=homeomorphism_inverse_continuous (inner_own_norm_homeomorphism (@euclidean_inner_productP R n)).
move=>D; exact:(continuous_comp (hEvaluation D) (hIdentity (D x))).
Qed.

(** Source for [euclidean_differential_top_word_continuous]: continuity
    of S as a function of D in 3.2.25, p. 261.
    Coordinate evaluations are continuous; the finite exterior
    product is continuous by 1.8.1, p. 38. Every
    natural degree, including the empty product, is retained. *)
Theorem euclidean_differential_top_word_continuous (R:realType) m n:
  continuous (fun D:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (euclidean_differential_top_word D:inner_metric_space (@exterior_inner_productP R
      (euclidean_two_nonzero R) (R_n R n) (@euclidean_inner_product R n)
      (@euclidean_inner_productP R n) m))).
Proof.
pose H:=real_norm_metric_space (@euclidean_operator_norm_is_norm R m n).
pose N:=inner_metric_space (@euclidean_inner_productP R n).
have hFamily:continuous (fun D:H=>fun i:'I_m=>(D (@coordinate_basis R m i):N)).
  apply:(@coordinate_family_continuous H [the eqType of 'I_m] (fun _=>[the topologicalType of N])).
  move=>i; exact:euclidean_operator_point_continuous.
have ho:orthonormal_family (@euclidean_inner_product R n) (@coordinate_basis R n).
  by move=>i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
have hProduct:=@exterior_product_continuous_orthonormal R (euclidean_two_nonzero R)
  (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
  n (@coordinate_basis R n) (@coordinate_basisP R n) ho m.
move=>D; exact:(continuous_comp (hFamily D) (hProduct (fun i=>D (@coordinate_basis R m i)))).
Qed.

(** Source for [euclidean_differential_orientation]: the formula
    T=S divided by its norm in 3.2.25, p. 261,
    as a pointwise expression on the already specified space
    of differentials. Its zero value is only auxiliary;
    chart differentials are proved injective before use. *)
Definition euclidean_differential_orientation (R:realType) m n (D:Hom (R_n R m) (R_n R n)):=
  inner_unit_normalization (@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m)
    (euclidean_differential_top_word D).

(** Source for [euclidean_differential_orientation_borel]: the
    measurable expression used to orient each compact chart in
    3.2.25, p. 261. Continuous exterior words and the
    Borel normalization compose without a default differential or
    an assumption on a selected derivative field. *)
Theorem euclidean_differential_orientation_borel (R:realType) m n:
  is_borel_function (fun D:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (euclidean_differential_orientation D:inner_metric_space (@exterior_inner_productP R
      (euclidean_two_nonzero R) (R_n R n) (@euclidean_inner_product R n)
      (@euclidean_inner_productP R n) m))).
Proof.
move=>U hU.
pose hE:=@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m.
have hNormalized:=@inner_unit_normalization_borel R (exterior_power (R_n R n) m)
  (@exterior_inner_form R (euclidean_two_nonzero R) (R_n R n) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) m) hE U hU.
exact:(continuous_borel_preimage (@euclidean_differential_top_word_continuous R m n) hNormalized).
Qed.
