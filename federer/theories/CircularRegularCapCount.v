(** Federer (1969), 3.3.19, p. 305: actual cyclic
    direction counts for every circular cap orientation. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric
  RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed CircularUnitVectors CircularRegularDirections
  CircularUnitVectorSurjection CircularAngleLift CircularCosineArcOrder
  CyclicGridShiftSeparation CyclicGridIntervalCount.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Section Count.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation p:=(@CircularTrigonometry.half_period R).

(** Source for [circular_regular_cap_subfamily_count]: among
    the actual original n circular directions, any subfamily
    lying in a cap of half-angle gamma has fraction at most
    gamma/pi+1/n. This supports the uniform cap-mass
    comparison in 3.3.19, p. 305. All orientations,
    closed contacts and both angular endpoints are retained. *)
Theorem circular_regular_cap_subfamily_count n (u:E) (gamma:R) (F:{fset 'I_n}):
  (0<n)%N ->inner_norm (@euclidean_inner_productP R 2) u= 1 ->
  0<=gamma ->gamma<=p ->
  (forall k,k \in F ->C gamma<=euclidean_inner_product (@circular_regular_direction R n k) u) ->
  #|` F|%:R/n%:R<=gamma/p+1/n%:R.
Proof.
move=>hn hu hGamma hGammaP hCap.
have hp:= real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R)).
have hpN:p!=0 by rewrite gt_eqF.
have hNP:(0<n%:R:>R) by rewrite ltr0n.
have hNN:(n%:R:R)!=0 by rewrite gt_eqF.
have [t [ht0 [ht2 hT]]]:= @circular_unit_vector_surjective R u hu.
have [a [hpa [hap hA]]]:= @circular_angle_central_representative R t ht0 ht2.
have hDirection:circular_unit_vector a= u by rewrite hA hT.
pose q:R:= 2* p/n%:R.
pose b:'I_n->bool:= circular_angle_lift_branch a.
have hq:0<q by rewrite /q divr_gt0 // mulr_gt0 // ltr0n.
have hWidth:a-gamma<=a+gamma by lra.
have hInside k:k \in F ->a-gamma<=cyclic_grid_shifted_point q b k /\
    cyclic_grid_shifted_point q b k<=a+gamma.
  move=>hk.
  have hDot:= hCap k hk.
  rewrite -hDirection /circular_regular_direction circular_unit_vector_inner in hDot.
  have hLift:= @circular_angle_lift_cosine R n a k hn.
  rewrite -hLift in hDot.
  have [hLower hUpper]:= @circular_angle_lift_bounds R n a k hn hpa hap.
  have hArc:=(@circular_cosine_arc_order R
    (cyclic_grid_shifted_point q b k-a) gamma hLower hUpper hGamma hGammaP).1 hDot.
  have /andP[hLeft hRight]:(-gamma<=cyclic_grid_shifted_point q b k-a<=gamma)
    by move:hArc;rewrite ler_norml.
  split;lra.
have hCount:= @cyclic_grid_interval_count R q n b F (a-gamma) (a+gamma) hq hWidth hInside.
have hReal:#|` F|%:R* q<=2* gamma+q by lra.
have hPositive:0<(2* p)^-1 by rewrite invr_gt0;nra.
have hScaled:= ler_wpM2r (ltW hPositive) hReal.
have hLeft:(#|` F|%:R* q)*(2* p)^-1=#|` F|%:R/n%:R.
  rewrite /q;field;by rewrite ?hNN ?hpN.
have hRight:(2* gamma+q)*(2* p)^-1= gamma/p+1/n%:R.
  rewrite /q;field;by rewrite ?hNN ?hpN.
by rewrite hLeft hRight in hScaled.
Qed.
End Count.
