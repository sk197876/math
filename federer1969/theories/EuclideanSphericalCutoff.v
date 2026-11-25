(** Federer (1969), 2.10.27, pp. 190–191: the sharp spherical section
    estimate at a fixed positive cutoff. Integrate source-indexed section
    majorants using 2.6.2 and 2.4.8, retaining repeated sections with their
    multiplicities. The auxiliary ball-volume witness is accessed only
    through its sealed profile laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates MetricCartesianProductUP MetricDiameter MetricClosedBalls
  EuclideanLebesgueDimensions EuclideanBallSectionProfile EuclideanBallSectionProfileUP
  SphericalEuclideanSections HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleCutoffCost MetricScaleApproximation
  CaratheodoryLimitUP NonnegativeSum MeasureUP MeasureBasic MeasureIndexedCover
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureUpperIntegralMonotone
  MeasureAlmostUP MeasureAlmostBasic TotalCountableNonnegativeIntegral ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_spherical_ball_section_majorant]:
    supporting single-ball integral in 2.10.27,
    p. 191. In positive ambient dimension, a
    source ball with diameter strictly below the
    target cutoff has a nonnegative integrable
    section majorant whose integral equals its cost.
    Boundary sections and degree zero are included. *)
Lemma euclidean_spherical_ball_section_majorant (R : realType) m n k
    (d : R) (nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (B : set (inner_metric_space (@euclidean_inner_productP R (m+n)))) :
  (0<m+n)%N ->
  is_metric_scale_envelope
    (fun j : @positive_closed_metric_balls R (inner_metric_space (@euclidean_inner_productP R n))=>val j)
    (fun j=>hausdorff_diameter_cost k (val j)) d%:E nu ->
  is_positive_metric_closed_ball B -> extended_metric_diameter B<d%:E ->
  exists q : inner_metric_space (@euclidean_inner_productP R m) -> extended_real_line R,
    (forall y, 0<=q y) /\
    is_measure_integral (@euclidean_lebesgue_measure R m) (partial_function_total q)
      (hausdorff_diameter_cost (k+m) B) /\
    forall y, nu (metric_product_section (fun a b=>@euclidean_block_join R m n (a,b)) B y)<=q y.
Proof.
move=> hdim hn [a [r [hr hB]]] hdiam.
have he : B=metric_closed_ball a r.
  apply/seteqP; split=> x hx; [exact: (hB x).1 hx | exact: (hB x).2 hx].
rewrite he in hdiam *.
have hrd : (r+r<d)%R.
  by rewrite (@positive_dimensional_euclidean_closed_ball_diameter R (m+n) a r hdim (ltW hr)) lte_fin in hdiam.
pose u := (@euclidean_block_split R m n a).1.
pose v := (@euclidean_block_split R m n a).2.
have ha : a= @euclidean_block_join R m n (u,v) by rewrite /u /v euclidean_block_splitK.
pose q := @euclidean_ball_section_profile R m k u r (ltW hr).
exists q; split; first exact: euclidean_ball_section_profile_nonnegative.
split.
- rewrite (@euclidean_positive_dimension_ball_cost R (m+n) (k+m) a r hdim (ltW hr)).
  exact: euclidean_ball_section_profile_integral.
- rewrite ha; move=> y.
  exact: (@spherical_ball_section_cutoff_bound R m n k u v r d nu q hn
    (@euclidean_ball_section_profile_specification R m k u r (ltW hr)) (ltW hr) hrd y).
Qed.

(** Source for [euclidean_spherical_cutoff_integral_bound]:
    supporting countable-cover integral estimate in
    2.10.27, p. 191. An arbitrarily fine source
    cover gives integrated majorants with total cost
    arbitrarily close to the spherical mass of A.
    No measurability of A or its sections is assumed.
    The ambient dimension is positive here; the
    empty Cartesian product is handled separately. *)
Theorem euclidean_spherical_cutoff_integral_bound (R : realType) m n k
    (A : set (inner_metric_space (@euclidean_inner_productP R (m+n)))) (d M : R)
    (nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :
  (0<m+n)%N -> (0<d)%R ->
  is_metric_scale_envelope
    (fun j : @positive_closed_metric_balls R (inner_metric_space (@euclidean_inner_productP R n))=>val j)
    (fun j=>hausdorff_diameter_cost k (val j)) d%:E nu ->
  @spherical_measure R (inner_metric_space (@euclidean_inner_productP R (m+n))) (k+m) A<=M%:E ->
  measure_upper_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y=>(nu (metric_product_section
      (fun a b=>@euclidean_block_join R m n (a,b)) A y) : extended_real_line R)))<=M%:E.
Proof.
move=> hdim hd hn hM.
apply: (@extended_upper_bound_from_scaled_errors R _ M 1%R ler01)=> e he.
rewrite mul1r.
pose P := inner_metric_space (@euclidean_inner_productP R (m+n)).
pose J := @positive_closed_metric_balls R P.
pose S := fun j : J=>val j.
pose c := fun j : J=>hausdorff_diameter_cost (k+m) (val j).
pose eta := (d/2)%R.
have heta : (0<eta)%R by rewrite /eta divr_gt0 // ltr0n.
have hetad : (eta<d)%R by rewrite /eta; lra.
pose xi := @metric_scale_envelope R P J S c eta%:E.
have hxi := @metric_scale_envelope_specification R P J S c eta%:E.
have hbound : xi A<(M+e)%R%:E.
  apply: le_lt_trans (@caratheodory_limit_upper R P J S c _
    (@spherical_measure_specification R P (k+m)) A eta%:E xi _ hxi) _.
  - by rewrite lte_fin.
  - apply: le_lt_trans hM _; rewrite lte_fin; lra.
have [G [hG [hdiam [hcover hcost]]]] := metric_scale_envelope_approximation hxi hbound.
have hmajor : forall j : J, exists q : inner_metric_space (@euclidean_inner_productP R m) -> extended_real_line R,
    G j -> (forall y, 0<=q y) /\
    is_measure_integral (@euclidean_lebesgue_measure R m) (partial_function_total q) (c j) /\
    forall y, nu (metric_product_section (fun a b=>@euclidean_block_join R m n (a,b)) (S j) y)<=q y.
  move=> j; case: (pselect (G j))=> hj.
  - have hsmall : extended_metric_diameter (S j)<d%:E.
      apply: le_lt_trans (hdiam j hj) _; by rewrite lte_fin.
    have [q hq] := @euclidean_spherical_ball_section_majorant R m n k d nu (S j)
      hdim hn (set_valP j) hsmall.
    exists q=> _; exact hq.
  - exists (fun _=>0); by move=> h; case: (hj h).
pose q := fun j : J=>projT1 (cid (hmajor j)).
have hq j (hj : G j) := projT2 (cid (hmajor j)) hj.
have hmu := @euclidean_lebesgue_is_measure R m.
have hint := @total_countable_nonnegative_integral R
  (inner_metric_space (@euclidean_inner_productP R m)) J _ hmu G q c hG
  (fun j hj=> (hq j hj).1) (fun j hj=> (hq j hj).2.1).
have hnu := metric_scale_envelope_is_measure hn (fun j=>hausdorff_diameter_cost_nonnegative k (val j)).
have hpoint y : nu (metric_product_section (fun a b=>@euclidean_block_join R m n (a,b)) A y)<=
    nonnegative_sum G (fun j=>q j y).
  apply: le_trans (@measure_indexed_cover R (inner_metric_space (@euclidean_inner_productP R n)) J
    nu hnu _ G (fun j=>metric_product_section (fun a b=>@euclidean_block_join R m n (a,b)) (S j) y) hG _) _.
  - move=> z hz; have [j hj hjz] := hcover (euclidean_block_join (y,z)) hz.
    by exists j.
  - apply: nonnegative_sum_mono=> j hj; exact: (hq j hj).2.2 y.
have hae : measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    (partial_extended_le_locus
      (partial_function_total (fun y=>(nu (metric_product_section (fun a b=>@euclidean_block_join R m n (a,b)) A y) : extended_real_line R)))
      (partial_function_total (fun y=>(nonnegative_sum G (fun j=>q j y) : extended_real_line R)))).
  apply: (@measure_almost_everywhere_mono R _ _ hmu setT _ _ (measure_almost_everywhere_true hmu)).
  move=> y _; exists (nu (metric_product_section (fun a b=>@euclidean_block_join R m n (a,b)) A y)),
    (nonnegative_sum G (fun j=>q j y)); split=> //; split=> //; exact: hpoint.
have hu := measure_upper_integral_monotone hmu hae.
have heq := measure_upper_integral_unique
  (measure_upper_integral_specification _ _) hint.2.1.
rewrite heq in hu; exact: le_trans hu (ltW hcost).
Qed.
