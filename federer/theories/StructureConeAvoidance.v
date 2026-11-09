(** Federer (1969), 3.3.5, p. 292: absence of original cones
    gives the printed inverse Lipschitz inequality on small subsets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanProjectionSpace StructureCone StructureProjectionKernel StructureProjectionCone
  MetricDiameterUP MetricDiameter MetricBiLipschitzUP LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_structure_cone_avoiding]: the original hypothesis
    E intersect X(a,r,ker p,s) is empty whenever a belongs to E,
    Federer 3.3.5, p. 292. No source measurability or measure is required. *)
Definition is_structure_cone_avoiding (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (r: \bar R) (s:R):=
  forall a,E a ->E `&` structure_cone (structure_projection_kernel hmn p) a r s=set0.

(** Source for [structure_cone_avoidance_inverse_distance]: the first
    inequality in the proof of Federer 3.3.5, p. 292. Original source
    points in a subset of diameter less than r cannot satisfy the
    strict cone inequality, so their original distances are at most
    s inverse times the distances of their actual projected values. *)
Theorem structure_cone_avoidance_inverse_distance (R:realType) n m (hmn:(m<=n)%N)
    (E S:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (r: \bar R) (s:R):
  0<s ->is_structure_cone_avoiding hmn E p r s ->S `<=` E ->
  (extended_metric_diameter S<r)%E ->
  forall a b,S a ->S b ->
    mdist a b<=s^-1*mdist
      (euclidean_projection_linear p a:inner_metric_space (@euclidean_inner_productP R m))
      (euclidean_projection_linear p b).
Proof.
move=>hs hAvoid hSE hDiameter a b ha hb.
have hNear:((inner_norm (@euclidean_inner_productP R n) (b-a))%:E<r)%E.
  have hPair:=metric_diameter_upper (extended_metric_diameter_specification S) ha hb.
  rewrite inner_metric_distanceE -[a-b]opprB inner_normN in hPair.
  exact:le_lt_trans hPair hDiameter.
have hNot:~structure_cone (structure_projection_kernel hmn p) a r s b.
  move=>hCone.
  have hBoth:(E `&` structure_cone (structure_projection_kernel hmn p) a r s) b by split; [exact:hSE b hb|exact:hCone].
  by rewrite (hAvoid a (hSE a ha)) in hBoth.
have hBound:inner_norm (@euclidean_inner_productP R n) (b-a)<=
    s^-1*inner_norm (@euclidean_inner_productP R m) (euclidean_projection_linear p (b-a)).
  rewrite leNgt; apply/negP=>hStrict; apply:hNot.
  apply/(structure_projection_coneE hmn p a r s b); by split.
rewrite !inner_metric_distanceE -linearB.
rewrite -[a-b]opprB inner_normN linearN inner_normN; exact:hBound.
Qed.

(** Source for [structure_cone_avoidance_bilipschitz]: the univalent
    projection restriction and its inverse bound in Federer 3.3.5,
    p. 292. The forward projection is already nonexpanding, and the
    absence of original cones supplies the actual inverse inequality. *)
Theorem structure_cone_avoidance_bilipschitz (R:realType) n m (hmn:(m<=n)%N)
    (E S:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (r: \bar R) (s:R):
  0<s<1 ->is_structure_cone_avoiding hmn E p r s ->S `<=` E ->
  (extended_metric_diameter S<r)%E ->
  @is_metric_bilipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R m)) S (euclidean_projection_linear p) s^-1.
Proof.
move=>/andP [hs hs1] hAvoid hSE hDiameter.
have hInv:0<s^-1 by rewrite invr_gt0.
have hIdentity:s*s^-1= 1 by rewrite mulfV // gt_eqF.
have hOne:1<=s^-1 by nra.
split.
- split; first exact:ltW hInv.
  move=>x y hx hy.
  apply:le_trans (euclidean_projection_nonexpanding p x y) _.
  have hN:0<=mdist x y:=mdist_ge0 x y.
  have hMul:=@ler_wpM2r R (mdist x y) hN 1 s^-1 hOne.
  by rewrite mul1r in hMul.
- exact:(@structure_cone_avoidance_inverse_distance R n m hmn E S p r s hs hAvoid hSE hDiameter).
Qed.
