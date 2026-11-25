(** Federer (1969), 3.3.17, p. 300: the actual
    finite regularisation retains the ORIGINAL conical densities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureCone StructureProjectionKernel StructureKernelOnto StructureInfiniteConeBorel
  StructureSmallConeCriterionUP MetricClosedBalls MetricDensities PositiveRadiusLimitCongruence
  MeasureUP MeasureRestriction TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_regularised_cone_upper_density]:
    the regularisation step in Federer 3.3.17, p. 300.
    Borel values on the ACTUAL cone intersect the actual closed
    ball identify EVERY original positive-radius quotient and
    hence the original upper density. Original E need not be
    measurable, and the actual density may be infinite. *)
Lemma structure_regularised_cone_upper_density (R:realType) n m (hmn:(m<=n)%N)
    (phi psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m)
    (a:inner_metric_space (@euclidean_inner_productP R n)) (s:R):
  (forall B,borel_set B ->psi B=phi (E `&` B)) ->
  upper_metric_density m (measure_restrict psi
    (structure_cone (structure_projection_kernel hmn p) a +oo s)) a=
  upper_metric_density m (measure_restrict phi
    (E `&` structure_cone (structure_projection_kernel hmn p) a +oo s)) a.
Proof.
move=>hValue.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose C:=structure_cone (structure_projection_kernel hmn p) a +oo s.
have hC:borel_set C:=structure_projection_infinite_cone_borel hmn p a s.
rewrite /upper_metric_density; apply:(positive_radius_limits_congr _).1=>r hr.
have hB:borel_set (C `&` metric_closed_ball a r).
  exact:(@borel_family_binary_intersection [the topologicalType of X] setT _
    (borel_sets_family [the topologicalType of X]) C _ hC
    (closed_borel_set (@metric_closed_ball_closed R [the metricType R of X] a r))).
rewrite /metric_ball_density /measure_restrict (hValue _ hB).
by rewrite setIA.
Qed.

(** Source for [structure_regularised_small_cone_criterion]:
    pointwise regularisation and local plane-to-projection step
    in Federer 3.3.17, p. 300. The actual onto kernel theorem
    supplies the original projection locally. Both original
    restricted upper densities and the exact s^m factor remain;
    no projection or plane field is globally selected. *)
Lemma structure_regularised_small_cone_criterion (R:realType) n m (hmn:(m<=n)%N)
    (phi psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n)):
  (forall B,borel_set B ->psi B=phi (E `&` B)) ->
  upper_metric_density m psi a=upper_metric_density m (measure_restrict phi E) a ->
  structure_small_cone_density_at m phi E a ->
  exists (p:euclidean_projection_space R n m) (s:R),(0<s<1)%R /\
    upper_metric_density m (measure_restrict psi
      (structure_cone (structure_projection_kernel hmn p) a +oo s)) a<
      (structure_small_cone_constant R m*s^+m)%:E*upper_metric_density m psi a.
Proof.
move=>hValue hDensity [V [s [hS hSmall]]].
have [p hKernel]:=@structure_projection_kernel_onto R n m hmn V.
exists p,s; split; first exact:hS.
rewrite (@structure_regularised_cone_upper_density R n m hmn phi psi E p a s hValue) hDensity hKernel.
exact:hSmall.
Qed.
