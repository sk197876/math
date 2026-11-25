(** Federer (1969), 3.2.36, p. 273: exact actual polar inner integral
    of the independently specified ball-section function. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanBallVolume EuclideanBallSectionProfile BallSectionSphereValue PositiveRadiusSphereMass
  SphereConstantIntegral RadialSphereIntegral PartialFunctionUP SummableRealFunctionUP
  MeasureIntegralUniqueness ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ball_section_radial_graph]: the actual radial integrand
    evaluating the coefficient c(xi,eta) in Federer 3.2.36, p. 273.
    The graph is exact at every positive radius: below or at r it is
    xi alpha(xi) alpha(eta) s^(xi-1) (r^2-s^2)^(eta/2),
    and beyond r it is zero. Sphere constancy, actual sphere mass and
    integral uniqueness prove both directions. The closed endpoint and
    the positive H^0 sphere atoms in dimension one are retained. *)
Lemma ball_section_radial_graph (R:realType) m k (r s:R) (hr:0<=r) a:
  (0<m)%N ->0<s ->
  (partial_function_graph
    (@radial_sphere_integral R m (real_total_integrand
      (fun y=>fine (@euclidean_ball_section_profile R m k 0 r hr y)))) s a <->
    (if s<=r then m%:R*euclidean_unit_ball_volume R m*
      euclidean_unit_ball_volume R k*s^+(m-1)*Num.sqrt (r^+2-s^+2)^+k else 0)%:E=a).
Proof.
move=>hm hs.
pose c:=if s<=r then euclidean_unit_ball_volume R k*Num.sqrt (r^+2-s^+2)^+k else 0.
have hc:0<=c.
  rewrite /c; case:ifP=>h; last exact:lexx.
  apply:mulr_ge0; first exact:ltW (euclidean_unit_ball_volumeE R k).2.
  apply:exprn_ge0; exact:sqrtr_ge0.
have hConst (y:R_n R m):inner_norm (@euclidean_inner_productP R m) y=s ->
    fine (@euclidean_ball_section_profile R m k 0 r hr y)=c.
  exact:ball_section_scalar_sphere_value.
have hI:=@sphere_constant_subset_integral R m (m-1) s c
  (fun y=>fine (@euclidean_ball_section_profile R m k 0 r hr y)) hc hConst.
rewrite (@positive_radius_sphere_mass R m s hm hs) -EFinM in hI.
have hAlg:c*(m%:R*euclidean_unit_ball_volume R m*s^+(m-1))=
    if s<=r then m%:R*euclidean_unit_ball_volume R m*
      euclidean_unit_ball_volume R k*s^+(m-1)*Num.sqrt (r^+2-s^+2)^+k else 0.
  rewrite /c; case:ifP=>h; last by rewrite mul0r.
  ring.
rewrite hAlg in hI.
rewrite radial_sphere_integral_graph; split.
- move=>ha; exact:measure_integral_unique hI ha.
- move=><-; exact hI.
Qed.
