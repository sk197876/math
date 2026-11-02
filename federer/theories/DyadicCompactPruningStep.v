(** Federer (1969), 2.10.47, p. 205: choose compact D_S in each level-j cell
    with finer content equal to the preceding content of E intersect S, and
    take their finite union. All intermediate values and null-overlap
    recombination are now proved for the actual real power contents. This is
    one induction step, not a postulated pruning sequence. Source context:
    DyadicContentDivisibility.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  DyadicCubeGridUP DyadicCubeGrid DyadicCubeGridLaws DyadicCubeOverlap DyadicContentSplitting
  DyadicContentDivisibility DyadicContentFinite DyadicContentNullSets CompactCellRecombination
  RefiningCoverContent MetricDiameter MetricRealPowerCost MetricRealPowerMeasureUP MetricRealPowerMeasureLaws
  MeasureUP MeasureBasic MeasureAlmostBasic MeasureRestriction NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dyadic_compact_pruning_step]: the choice
    of D_S and E_(j+1) in 2.10.47, p. 205.
    The retained set has the preceding total mass under
    the finer content and preserves each local target.
    No measurability of the chosen compact pieces for
    the fixed content is assumed. *)
Theorem dyadic_compact_pruning_step (R : realType) n (a : R_n R n) Q c p j gamma eta
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (E : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_dyadic_cube_grid a Q ->
  is_refining_cover_content (dyadic_cube_level Q) (metric_real_diameter_cost c p) j gamma ->
  is_refining_cover_content (dyadic_cube_level Q) (metric_real_diameter_cost c p) j.+1 eta ->
  is_metric_real_power_measure c p mu -> (0<n)%N -> (0<c)%R -> (0<p)%R -> compact E ->
  (forall x, E x -> forall l, (a l<=x l<=a l+1)%R) ->
  (forall (l : 'I_n) (t : R), mu (E `&` [set x | x l=t])=0) ->
  exists K, [/\ compact K, K `<=` E,
    (forall s, eta (K `&` @Q j s)=gamma (E `&` @Q j s)) & eta K=gamma E].
Proof.
move=> hQ hg he hmu hn hc hp hE hroot hlevels.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose l : 'I_n := Ordinal hn.
have hcost (T : set X) : 0<=metric_real_diameter_cost c p T :=
  @metric_real_power_cost_nonnegative R c p (extended_metric_diameter T) (ltW hc).
have hgm := refining_cover_content_measure hg (fun T _=>hcost T).
have hem := refining_cover_content_measure he (fun T _=>hcost T).
have hmm := metric_real_power_measure_law (ltW hc) hmu.
have hetanull (k : 'I_n) (t : R) : eta (E `&` [set x | x k=t])=0.
  exact (@dyadic_content_null_set R n a Q c p j.+1 eta mu (E `&` [set x | x k=t]) hQ he hmu hn (ltW hc) hp
    (fun x hx=>hroot x hx.1) (hlevels k t)).
have hover s t : s != t -> eta ((E `&` @Q j s) `&` @Q j t)=0.
  move=> hne; have [k [b hb]] := @dyadic_cube_distinct_overlap_hyperplane R n a Q hQ j s t hne.
  apply: (@measure_null_subset R X eta hem _ (E `&` [set x | x k=b])); last exact: hetanull.
  move=> x [[hxE hxs] hxt]; split=> //; apply: hb; by split.
have hchoose s : exists D, [/\ compact D, D `<=` (E `&` @Q j s) & eta D=gamma (E `&` @Q j s)].
  pose T := E `&` @Q j s.
  have hT : compact T := compact_closedI hE
    (compact_closed (@metric_hausdorff R X) (@dyadic_cube_compact R n a Q hQ j s)).
  have hTro : forall x, T x -> forall k, (a k<=x k<=a k+1)%R by move=> x hx; exact: hroot x hx.1.
  have hfin := @dyadic_power_content_root_finite R n a Q c p j gamma hQ hg (ltW hc) (ltW hp) T hTro.
  have hnum : gamma T \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hgm T)).
  pose y := fine (gamma T).
  have hyE : gamma T=y%:E := esym (fineK hnum).
  have hy : (0<=y)%R by have hh := measure_nonnegative hgm T; rewrite hyE lee_fin in hh.
  have hyle : y%:E<=eta T.
    rewrite -hyE; exact (@refining_cover_content_nondecreasing R X (dyadic_cube_level Q)
      (metric_real_diameter_cost c p) j j.+1 gamma eta hg he (fun U _=>hcost U) (leqnSn j) T).
  have hTl t : mu (T `&` [set x | x l=t])=0.
    apply: (@measure_null_subset R X mu hmm _ (E `&` [set x | x l=t])); last exact: hlevels.
    by move=> x [[hx _] ht]; split.
  have [D [hDc hDs hDv]] := @dyadic_content_intermediate_compact_subset R n a Q c p j.+1 eta
    mu T l y hQ he hmu hc hp hT hTro hTl hy hyle.
  exists D; split=> //; by rewrite hyE.
have [K [hK hKE hlocal]] := @compact_cell_recombination R X (dyadic_cube_indices n j)
  eta hem E (@Q j) (fun s=>gamma (E `&` @Q j s)) hover hchoose.
exists K; split=> //.
have hKroot x (hx : K x) := hroot x (hKE x hx).
have hKnull (k : 'I_n) (t : R) : eta (K `&` [set x | x k=t])=0.
  apply: (@measure_null_subset R X eta hem _ (E `&` [set x | x k=t])); last exact: hetanull.
  by move=> x [hx ht]; split; first exact: hKE.
have hEnull (k : 'I_n) (t : R) : gamma (E `&` [set x | x k=t])=0.
  exact (@dyadic_content_null_set R n a Q c p j gamma mu (E `&` [set x | x k=t]) hQ hg hmu hn (ltW hc) hp
    (fun x hx=>hroot x hx.1) (hlevels k t)).
rewrite (@dyadic_content_level_additivity R n a Q K _ j.+1 eta j hQ he (fun T _=>hcost T)
  hKnull hKroot (leqnSn j)).
rewrite (@dyadic_content_level_additivity R n a Q E _ j gamma j hQ hg (fun T _=>hcost T)
  hEnull hroot (leqnn j)).
apply: nonnegative_sum_ext=> s _; exact: hlocal.
Qed.
