(** Federer (1969), 3.2.30, p. 268: linear maps multiply
    exterior endpoint costs by at most the norm of the actual
    induced exterior map, as follows from 2.10.3, pp. 171–172. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps InnerMetric
  ExteriorGrading FiniteExteriorPowers ExteriorMaps ExteriorNorm ExteriorOperatorEstimate ExteriorOperatorNorm
  OperatorNormUP EuclideanLinearJacobian ExteriorDiameterUP ExteriorDiameterLaws ExteriorDiameter
  ExteriorMeasureGauge HausdorffDiameterCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [exterior_linear_endpoint_bound]: the endpoint
    estimate underlying Federer 3.2.30, p. 268, by the
    exterior functor in 1.3.1 and operator norm of 1.7.6.
    All natural degrees, singular maps and ambient dimensions
    are retained in this supporting pointwise estimate. *)
Lemma exterior_linear_endpoint_bound (R:realType) s n k
    (L:Hom (R_n R s) (R_n R n)) (a b:'I_k->R_n R s):
  exterior_difference_norm (fun i=>L (a i)) (fun i=>L (b i))<=
    euclidean_linear_jacobian k L*exterior_difference_norm a b.
Proof.
have hFamily:(fun i:'I_k=>hom_as_linear L (a i-b i))=(fun i=>L (a i)-L (b i)).
  by apply:funext=>i; rewrite linearB.
have hWord:exterior_power_map (hom_as_linear L) k (exterior_difference_product a b)=
    exterior_difference_product (fun i=>L (a i)) (fun i=>L (b i)).
  by rewrite /exterior_difference_product exterior_map_indexed_product hFamily.
have hh:=operator_norm_vector_bound (@exterior_operator_normP R (euclidean_two_nonzero R)
  (R_n R s) (R_n R n) (@euclidean_inner_product R s) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R s) (@euclidean_inner_productP R n)
  s (@coordinate_basis R s) (@coordinate_basisP R s) (hom_as_linear L) k)
  (exterior_difference_product a b).
change (is_true (exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
  (exterior_power_map (hom_as_linear L) k (exterior_difference_product a b))<=
  euclidean_linear_jacobian k L*exterior_norm (euclidean_two_nonzero R)
    (@euclidean_inner_productP R s) (exterior_difference_product a b))) in hh.
rewrite hWord in hh.
by rewrite /exterior_difference_norm
  (Prop_irrelevance (real_exterior_two_nonzero R) (euclidean_two_nonzero R)).
Qed.

(** Source for [exterior_linear_diameter_bound]: supporting
    supremum estimate for Federer 3.2.30, p. 268, directly
    from the defining endpoint supremum in 2.10.3, p. 171.
    Infinite source diameter, zero norm and empty sets are allowed
    with the existing extended nonnegative multiplication convention. *)
Theorem exterior_linear_diameter_bound (R:realType) s n k
    (L:Hom (R_n R s) (R_n R n)) (A:set (R_n R s)):
  (extended_exterior_diameter k (L @` A)<=
    (euclidean_linear_jacobian k L)%:E*extended_exterior_diameter k A)%E.
Proof.
pose J:=euclidean_linear_jacobian k L.
have hJ:0<=J:=euclidean_linear_jacobian_nonnegative k L.
apply:(exterior_diameter_least_bound (extended_exterior_diameter_specification k (L @` A))).
- apply:mule_ge0; first by rewrite lee_fin.
  exact:exterior_diameter_nonnegative (extended_exterior_diameter_specification k A).
- move=>a b ha hb.
  have hexA i:exists x,A x /\a i=L x.
    have [x hx he]:=ha i; exists x; split; first exact hx; exact:esym he.
  have hexB i:exists x,A x /\b i=L x.
    have [x hx he]:=hb i; exists x; split; first exact hx; exact:esym he.
  have [aa hAA]:=choice hexA.
  have [bb hBB]:=choice hexB.
  have haE:a=(fun i=>L (aa i)) by apply:funext=>i; exact:(hAA i).2.
  have hbE:b=(fun i=>L (bb i)) by apply:funext=>i; exact:(hBB i).2.
  rewrite haE hbE.
  apply:le_trans (lee_tofin (exterior_linear_endpoint_bound L aa bb)) _.
  rewrite EFinM; apply:lee_wpmul2l; first by rewrite lee_fin.
  exact:exterior_diameter_endpoint_upper (extended_exterior_diameter_specification k A)
    (fun i=>(hAA i).1) (fun i=>(hBB i).1).
Qed.

(** Source for [exterior_linear_cost_bound]: the normalized
    cost estimate in the first inequality of Federer 3.2.30,
    p. 268. The source and target normalizing coefficient
    is the same actual alpha(k)/2^k of 2.10.3, p. 171. *)
Theorem exterior_linear_cost_bound (R:realType) s n k
    (L:Hom (R_n R s) (R_n R n)) (A:set (R_n R s)):
  (exterior_diameter_cost k (L @` A)<=
    (euclidean_linear_jacobian k L)%:E*exterior_diameter_cost k A)%E.
Proof.
rewrite /exterior_diameter_cost muleCA.
apply:lee_wpmul2l.
- rewrite lee_fin; exact:ltW (hausdorff_normalisation_positive R k).
- exact:exterior_linear_diameter_bound.
Qed.
