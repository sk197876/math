(** Federer (1969), 2.10.24, p. 188: supporting comparison between weighted
    spherical and Hausdorff constructions. An injective inclusion of
    generator families preserves finite real weights; null-set transfer
    supplies the almost-everywhere reference-measure comparison. This
    supports a repair using 2.10.2(2), p. 171, instead of the false
    Hausdorff-closed-ball-family remark on p. 188. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MetricDiameter MeasureUP MeasureAlmostUP MeasureAlmostBasic
  NonnegativeSum NonnegativeSumSupport NonnegativeSumProduct NonnegativeSumImageBound
  WeightedMetricEnvelopeUP WeightedMetricEnvelope WeightedMetricLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_cover_injective_transport]: supporting
    finite-real cover transfer for the spherical application
    of 2.10.24, p. 188. Injectivity avoids merging
    repeated images; weights outside the image are zero.
    Every actual source hypothesis is transported explicitly. *)
Theorem weighted_cover_injective_transport (R : realType) (X : metricType R) (J K : choiceType)
    (S : J -> set X) (T : K -> set X) (c : J -> \bar R) (d : K -> \bar R)
    (psi mu : set X -> \bar R) (q : J -> K) (delta : \bar R)
    (f : X -> \bar R) (G : set J) (u : J -> R) :
  is_measure mu -> injective q -> (forall k, 0<=d k) ->
  (forall N, psi N=0 -> mu N=0) -> (forall j, S j `<=` T (q j)) ->
  (forall j, extended_metric_diameter (T (q j))<=extended_metric_diameter (S j)) ->
  (forall j, d (q j)<=c j) -> is_weighted_metric_cover S psi delta f G u ->
  exists v : K -> R, is_weighted_metric_cover T mu delta f (q @` G) v /\
    weighted_generator_cost d (q @` G) v<=weighted_generator_cost c G u.
Proof.
move=> hm hq hd hnull hST hdiam hcost hcover.
have hu0 j (hj : G j) : (0<=u j)%R := @weighted_metric_cover_nonnegative R X J S psi delta f G u hcover j hj.
pose v k := match pselect (exists j, q j=k) with
  | left hk=>u (projT1 (cid hk))
  | right _=>0%R
  end.
have hv j : v (q j)=u j.
  rewrite /v; case: (pselect (exists i, q i=q j))=> [hj|hj].
  - have he := projT2 (cid hj); have hji := hq _ _ he; by rewrite hji.
  - exfalso; apply: hj; by exists j.
have hU : countable (q @` G) := sub_countable (card_image_le q G) (weighted_metric_cover_countable hcover).
have hv0 k : (q @` G) k -> (0<=v k)%R.
  move=> [j hj <-]; rewrite hv; exact: hu0 j hj.
have hpoint x : weighted_generator_sum S G u x<=weighted_generator_sum T (q @` G) v x.
  pose A := [set j | G j /\ S j x].
  have he : weighted_generator_sum S G u x=nonnegative_sum (q @` A) (fun k=>(v k)%:E).
    rewrite nonnegative_sum_injective_image.
    + apply: nonnegative_sum_ext=> j [hj hxj]; by rewrite hv.
    + by move=> j i _ _ he; exact: hq _ _ he.
    + move=> j [hj _]; rewrite hv lee_fin; exact: hu0 j hj.
  rewrite he; apply: nonnegative_sum_subset=> k [j [hj hxj] <-]; split.
  - by exists j.
  - exact: hST j x hxj.
have hdomS : measure_almost_everywhere mu [set x | f x<=weighted_generator_sum S G u x].
  exact: hnull _ (weighted_metric_cover_dominates hcover).
have hnew : is_weighted_metric_cover T mu delta f (q @` G) v.
  constructor; [exact hU|exact hv0| |].
  - move=> k [j hj <-]; exact: le_trans (hdiam j) (weighted_metric_cover_diameter hcover hj).
  - apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hdomS)=> x hx.
    exact: le_trans hx (hpoint x).
exists v; split=> //.
apply: le_trans (@nonnegative_sum_image_bound R J K G q (fun k=>(v k)%:E*d k) _) _.
- move=> j hj; apply: mule_ge0; [rewrite hv lee_fin; exact: hu0 j hj|exact: hd].
- apply: nonnegative_sum_mono=> j hj; rewrite hv.
  apply: lee_wpmul2l; [rewrite lee_fin; exact: hu0 j hj|exact: hcost].
Qed.

(** Source for [weighted_limit_injective_transport]: supporting
    weighted cutoff-limit comparison for the repair of
    the spherical application of 2.10.24, p. 188.
    The null-transfer hypothesis is supplied by the
    proved Hausdorff/spherical measure comparison. *)
Theorem weighted_limit_injective_transport (R : realType) (X : metricType R) (J K : choiceType)
    (S : J -> set X) (T : K -> set X) (c : J -> \bar R) (d : K -> \bar R)
    (psi mu : set X -> \bar R) (q : J -> K)
    (L : (X -> \bar R) -> \bar R) (M : (X -> \bar R) -> \bar R) (f : X -> \bar R) :
  is_measure mu -> injective q -> (forall k, 0<=d k) ->
  (forall N, psi N=0 -> mu N=0) -> (forall j, S j `<=` T (q j)) ->
  (forall j, extended_metric_diameter (T (q j))<=extended_metric_diameter (S j)) ->
  (forall j, d (q j)<=c j) ->
  is_weighted_metric_limit S c psi L -> is_weighted_metric_limit T d mu M -> M f<=L f.
Proof.
move=> hm hq hd hnull hST hdiam hcost hL hM.
apply: (weighted_metric_limit_least hM)=> delta lambda hdelta hlambda.
pose eta := weighted_metric_envelope S c psi delta.
have heta := @weighted_metric_envelope_specification R X J S c psi delta.
apply: le_trans _ (@weighted_metric_limit_upper R X J S c psi L hL f delta eta hdelta heta).
apply: (weighted_metric_envelope_greatest heta)=> G u hcover.
have [v [hnew hnewcost]] := @weighted_cover_injective_transport R X J K S T c d psi mu q delta f G u
  hm hq hd hnull hST hdiam hcost hcover.
exact: le_trans (weighted_metric_envelope_lower hlambda hnew) hnewcost.
Qed.
