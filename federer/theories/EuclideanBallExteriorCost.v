(** Centred-ball cost in Federer (1969), 2.10.32, p. 197: the
    exterior-diameter cost of the closed ball of radius r is alpha(n) r^n,
    equal to its Lebesgue volume. Opposite scaled orthonormal basis points
    attain the required endpoint norm; the product-norm inequality supplies
    the reverse bound. Use the actual project unit-ball coefficient and the
    full normalisation alpha(n) 2^(-n). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct CoordinateProjection
  InnerNorm InnerMetric InnerNormalization OrthonormalFamilies ExteriorGrading FiniteExteriorPowers
  ExteriorProductFactors ExteriorNorm ExteriorDiameterUP ExteriorDiameterLaws ExteriorDiameter
  ExteriorDiameterBound ExteriorMeasureGauge MetricClosedBalls MetricDiameterUP MetricDiameter
  EuclideanBallVolume EuclideanClosedBallVolume EuclideanLebesgueDimensions HausdorffDiameterCost HausdorffRadiusCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_closed_ball_exterior_cost]: direct
    equality zeta B(0,r)=alpha(n) r^n
    in 2.10.32, p. 197. The supremum
    is bounded above and attained by opposite
    scaled coordinate basis points; its sealed
    implementation is not unfolded. *)
Theorem euclidean_closed_ball_exterior_cost (R : realType) (n : nat) (r : R) :
  0<=r -> exterior_diameter_cost n (metric_closed_ball
    (0 : inner_metric_space (@euclidean_inner_productP R n)) r)=
    (euclidean_unit_ball_volume R n*r^+n)%:E.
Proof.
move=> hr.
pose hB := @euclidean_inner_productP R n.
pose A := metric_closed_ball (0 : inner_metric_space hB) r.
pose c := hausdorff_normalisation R n.
have hc : (0<=c%:E)%E by rewrite lee_fin; exact: ltW (hausdorff_normalisation_positive R n).
have hrr : 0<=r+r := addr_ge0 hr hr.
have hdiam : (extended_metric_diameter A<=(r+r)%:E)%E.
  apply: (metric_diameter_least (extended_metric_diameter_specification A)).
  - by rewrite lee_fin.
  - move=> x y hx hy; rewrite lee_fin; exact: metric_closed_ball_diameter_bound hx hy.
have hext := @extended_exterior_diameter_metric_bound R n n A (r+r) hrr hdiam.
have hupper := lee_wpmul2l hc hext.
rewrite -EFinM /c hausdorff_doubled_radius_normalisation in hupper.
have ho : orthonormal_family (@euclidean_inner_product R n) (@coordinate_basis R n).
  by move=> i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
have hnorm i : inner_norm hB (@coordinate_basis R n i)= 1 := orthonormal_norm1 hB ho i.
pose p (i : 'I_n) := r*:(@coordinate_basis R n i).
pose q (i : 'I_n) := (-r)*:(@coordinate_basis R n i).
have hp i : A (p i).
  by rewrite /A /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN /p inner_normZ hnorm mulr1 ger0_norm.
have hq i : A (q i).
  by rewrite /A /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN /q inner_normZ hnorm mulr1 normrN ger0_norm.
have hfamily : (fun i=>p i-q i)=(fun i=>(r+r)*:(@coordinate_basis R n i)).
  by apply: funext=> i; rewrite /p /q -scalerBl opprK.
have hproduct : exterior_difference_product p q=
    (r+r)^+n*:e_lambda (@coordinate_basis R n) (ord_tuple n).
  by rewrite /exterior_difference_product hfamily exterior_product_scaled_family prodr_const card_ord.
have heq : exterior_difference_norm p q=(r+r)^+n.
  rewrite /exterior_difference_norm hproduct exterior_norm_scale normrX (ger0_norm hrr).
  by rewrite (@orthonormal_product_unit_norm R (real_exterior_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) hB n (@coordinate_basis R n) ho) mulr1.
have hs := exterior_diameter_endpoint_upper (extended_exterior_diameter_specification n A) hp hq.
have hlower := lee_wpmul2l hc hs.
change (is_true (((c*exterior_difference_norm p q)%:E<=exterior_diameter_cost n A)%E)) in hlower.
rewrite heq /c hausdorff_doubled_radius_normalisation in hlower.
apply/eqP; by rewrite eq_le hupper hlower.
Qed.

(** Source for [euclidean_closed_ball_exterior_volume]: direct
    middle equality between actual Lebesgue volume
    and zeta B(0,r) in 2.10.32, p. 197.
    The closed-ball volume formula was proved
    separately from open approximation in 2.10.27. *)
Corollary euclidean_closed_ball_exterior_volume (R : realType) (n : nat) (r : R) :
  0<=r -> exterior_diameter_cost n (metric_closed_ball
    (0 : inner_metric_space (@euclidean_inner_productP R n)) r)=
    euclidean_lebesgue_measure n (metric_closed_ball
      (0 : inner_metric_space (@euclidean_inner_productP R n)) r).
Proof.
move=> hr; rewrite (@euclidean_closed_ball_exterior_cost R n r hr).
by rewrite (@euclidean_closed_ball_normalized_volume R n
  (0 : inner_metric_space (@euclidean_inner_productP R n)) r hr).
Qed.
