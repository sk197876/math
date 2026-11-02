(** Federer (1969), 3.2.13, p. 250: removing
    the actual radial Jacobian from the coarea integral.
    Its value is one away from the null origin;
    no Jacobian default at the origin is used. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanRadialDifferential
  EuclideanLebesgueDimensions ApproximateDifferentialAffine Jacobian JacobianUP
  EuclideanTargetJacobianMeasurable PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition
  PartialDensityProduct MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [radial_extended_jacobian_one_graph]: the
    actual graph value J_1 f(x)=1 for x nonzero,
    Federer 3.2.13, p. 250. It retains
    the genuine differential domain. *)
Lemma radial_extended_jacobian_one_graph (R:realType) m (x:R_n R m):
  x!=0 ->partial_function_graph (extended_euclidean_target_jacobian
    (@euclidean_radial_norm R m)) x (1%R)%:E.
Proof.
move=>hx; exists (1:R); split=>//.
apply:(euclidean_jacobian_graph 1 setT (@euclidean_radial_norm R m) x 1).2.
exists (euclidean_radial_gradient x); split.
- exact:euclidean_radial_differential hx.
- exact:euclidean_radial_jacobian_one hx.
Qed.

(** Source for [radial_jacobian_density_almost_equal]: the
    removal of J_1 f=1 from the source integral
    in Federer 3.2.13, p. 250. Positive
    dimension ensures the origin has zero Lebesgue measure;
    an arbitrary measurable partial integrand is retained. *)
Lemma radial_jacobian_density_almost_equal (R:realType) m
    (u:partial_function (R_n R m) (extended_real_line R)):
  (0<m)%N ->is_measure_measurable_function (@euclidean_lebesgue_measure R m) u ->
  measure_almost_equal (@euclidean_lebesgue_measure R m)
    (partial_density_product u (extended_euclidean_target_jacobian (@euclidean_radial_norm R m))) u.
Proof.
case:m u=>[u hBad|m u _ hu]; first by [].
pose mu:=@euclidean_lebesgue_measure R m.+1.
pose hm:=euclidean_lebesgue_is_measure R m.+1.
have hAway:measure_almost_everywhere mu [set x:R_n R m.+1|x!=0].
  have hEq:(~` [set x:R_n R m.+1|x!=0])=[set (0:R_n R m.+1)].
    apply/seteqP; split=>x.
    - move=>hx; case:(eqVneq x 0)=>[he|hne].
      + by rewrite he.
      + exfalso; exact:hx hne.
    - move=>hx hn.
      have he:x=0 by exact hx.
      move:hn; change (x!=0 ->False).
      by rewrite he eqxx.
  rewrite /measure_almost_everywhere hEq.
  exact:positive_euclidean_singleton_null.
have hBoth:=measure_almost_everywhere_and hm hAway (measurable_function_domain hu).
apply:(measure_almost_everywhere_mono hm _ hBoth)=>x [hx [z hz]].
exists z; split=>//.
apply/partial_density_product_graph; exists z,(1%R)%:E; split=>//; split.
- exact:radial_extended_jacobian_one_graph hx.
- exact:mule1.
Qed.
