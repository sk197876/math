(** Federer 2.10.27, p. 191: the exact unit-sphere
    integrand for the auxiliary real-coordinate ball integral.
    Reuse finite subset scaling and the independently proved
    sphere-coordinate moment, rather than a new angular assumption
    in the final profile theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HausdorffMeasure RealPower RealPowerSuccessor RealPowerNaturalHausdorff RealPowerRadialIntegral
  UnitBallCoordinatePowerSummability RealSubsetFiniteScale PolarUnitSphereIntegral
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralGraphEquivalence MeasureConullZeroIntegral SummableRealFunctionUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition PartialZeroExtension
  PartialDensityProduct ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [coordinate_power_weighted_radius]: supporting
    radial homogeneity in the profile evaluation of Federer
    2.10.27, p. 191. Combine the actual real power with the
    natural Jacobian power, including negative coordinate exponents. *)
Lemma coordinate_power_weighted_radius (R:realType) n (q r:R):
  (0<n)%N ->0<r ->real_power r q*r^+(n-1)=real_power r (q+n%:R-1).
Proof.
move=> hn hr.
have hCast:((n-1)%:R:R)+1=n%:R.
  have hNat:(n-1+1=n)%N:=subnK hn.
  have h:=congr1 (fun k:nat=>(k%:R:R)) hNat.
  by rewrite natrD in h.
have hPred:((n-1)%:R:R)=n%:R-1 by lra.
have hExp:q+((n-1)%:R:R)=q+n%:R-1 by rewrite hPred;ring.
by rewrite -(@real_power_natural_exponent R r (n-1) (ltW hr))
  -(@real_power_add_exponents_positive R r q ((n-1)%:R:R) hr) hExp.
Qed.

(** Source for [unit_ball_coordinate_weighted_sphere_value]: the
    exact positive-radius sphere integral underlying the real-degree
    profile identity in Federer 2.10.27, p. 191. This connection
    accepts an independently proved finite angular integral; the final
    application supplies its actual Gamma value from 3.2.13. *)
Lemma unit_ball_coordinate_weighted_sphere_value (R:realType) n (i:'I_n) (q:R)
    (g:inner_metric_space (@euclidean_inner_productP R n)->R) (b r:R):
  (0<n)%N ->0<r ->is_unit_ball_coordinate_power i q g ->
  is_measure_subset_integral
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) (n-1))
    [set u|inner_norm (@euclidean_inner_productP R n) u = 1]
    (real_total_integrand (fun u:inner_metric_space (@euclidean_inner_productP R n)=>real_power `|u i| q)) b%:E ->
  partial_function_graph (weighted_unit_sphere_integral (real_total_integrand g)) r
    (b*positive_radius_power (q+n%:R) 1 r)%:E.
Proof.
move=> hn hr hg hAngular.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X (n-1).
pose hH:=@hausdorff_measure_is_measure R X (n-1).
pose S:set X:=[set u|inner_norm (@euclidean_inner_productP R n) u = 1].
have hNorm u:S u ->inner_norm (@euclidean_inner_productP R n) (r*:u)=r.
  by move=> hu;rewrite inner_normZ (ger0_norm (ltW hr)) hu mulr1.
case:(leP r 1)=>hCap.
- rewrite /positive_radius_power hr hCap.
  pose c:=real_power r q.
  have hc:c!=0:=lt0r_neq0 (real_power_strictly_positive q hr).
  have hSep u:S u ->g (r*:u)=c*real_power `|u i| q.
    move=> hu.
    have hBall:inner_norm (@euclidean_inner_productP R n) (r*:u)<=1 by rewrite hNorm.
    rewrite (hg.1 (r*:u) hBall) ffunE normrM (ger0_norm (ltW hr)).
    exact:real_power_product (ltW hr) (normr_ge0 (u i)).
  have hMul:=@real_subset_integral_multiply_finite_scale R X H hH S
    (fun u=>g (r*:u)) (fun u:inner_metric_space (@euclidean_inner_productP R n)=>real_power `|u i| q) b c hc hSep hAngular.
  have hUnit:partial_function_graph
      (unit_sphere_dilation_integral (real_total_integrand g)) r (c*b)%:E.
    apply/unit_sphere_dilation_integral_graph.
    apply:(measure_integral_graph_equivalent _ hMul)=>u z;by [].
  apply/partial_density_product_graph;exists (c*b)%:E,(r^+(n-1))%:E.
  split=> //;split;first by [].
  rewrite -EFinM.
  have hProduct:(c*b)*r^+(n-1)=b*(c*r^+(n-1)) by ring.
  by rewrite hProduct /c (@coordinate_power_weighted_radius R n q r hn hr).
- have hNot:~~(0<r<=1).
    apply/negP=>/andP [_ h];have:=lt_le_trans hCap h;by rewrite ltxx.
  rewrite /positive_radius_power (negbTE hNot) mulr0.
  have hZero:is_measure_subset_integral H S (real_total_integrand (fun u=>g (r*:u))) 0%E.
    apply:(@measure_almost_zero_integral R X H hH _).
    apply:(@measure_almost_everywhere_mono R X H hH setT _ _
      (measure_almost_everywhere_true hH))=>u _.
    apply/partial_function_zero_extension_graph;case:(pselect (S u))=>hu.
    + left;split=> //;apply/real_total_integrand_graph.
      have hOut:1<inner_norm (@euclidean_inner_productP R n) (r*:u) by rewrite hNorm.
      by rewrite (hg.2 _ hOut).
    + by right.
  have hUnit:partial_function_graph
      (unit_sphere_dilation_integral (real_total_integrand g)) r 0%E.
    apply/unit_sphere_dilation_integral_graph.
    apply:(measure_integral_graph_equivalent _ hZero)=>u z;by [].
  apply/partial_density_product_graph;exists 0%E,(r^+(n-1))%:E.
  split=> //;split;first by [].
  exact:mul0e.
Qed.
