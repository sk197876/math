(** Federer (1969), 3.3.6, p. 294: the upper density
    consequence of the actual original cylinder mass estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureCone StructureProjectionKernel StructurePureConeMass RectifiableSetUP
  MeasureUP MeasureBasic MeasureRestriction MetricClosedBalls EuclideanBallVolume
  MetricDensities PositiveRadiusLimitBounds ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_pure_cone_upper_density]: the last sentence
    of Federer 3.3.6, p. 294. Actual original restricted ball masses
    are bounded by the proved cylinder masses at every sufficiently
    small positive real radius; the full-radius upper limit and
    positive normalization give the exact printed density coefficient. *)
Theorem structure_pure_cone_upper_density (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))-> \bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (e lam:R) (xi: \bar R)
    (a:inner_metric_space (@euclidean_inner_productP R n)):
  is_purely_measure_m_unrectifiable phi m A ->0<e<1 ->0<=lam ->(0<xi)%E ->
  (forall x,A x ->forall r:R,0<r ->(r%:E<=xi)%E ->
    (phi (A `&` structure_cone (structure_projection_kernel hmn p) x r%:E (4*e))<=
      (lam*euclidean_unit_ball_volume R m*r^+m*(4*e)^+m)%:E)%E) ->
  (upper_metric_density m (measure_restrict phi A) a<=(2*84^+m*lam)%:E)%E.
Proof.
move=>hPure he hLam hXi hMass.
have [he0 he1]:=andP he.
have [q [hq0 hqXi]]:=@extended_rationals_order_dense R 0 xi hXi.
pose t:R:=ratr q.
have ht:0<t:=hq0.
pose delta:=e*t/6.
have hNumerator:0<e*t:=mulr_gt0 he0 ht.
have hDelta:0<delta by rewrite /delta divr_gt0 // ltr0n.
apply:(@positive_radius_upper_eventual_bound R _ _ delta hDelta)=>r /andP[hr hrDelta].
have hCutoff:((6*r/e)%:E<=xi)%E.
  have hSmall:6*r/e<=t.
    rewrite ler_pdivrMr //; rewrite /delta in hrDelta; nra.
  exact:le_trans (lee_tofin hSmall) (ltW hqXi).
have hCylinder:=@structure_pure_cone_local_mass R n m hmn phi A p e lam r xi a
  hPure he hLam hr hCutoff hMass.
have hRadius:r<=r/e by rewrite ler_pdivlMr //; nra.
have hSub:(A `&` metric_closed_ball a r) `<=`
    (A `&` metric_closed_ball a (r/e) `&`
      ((euclidean_projection_linear p) @^-1`
        metric_closed_ball (euclidean_projection_linear p a:inner_metric_space (@euclidean_inner_productP R m)) r)).
  move=>x [hx hNear]; split; first split; first exact:hx.
  - exact:le_trans hNear hRadius.
  - apply:le_trans (euclidean_projection_nonexpanding p a x) hNear.
have hBound:=le_trans (@measure_mono R _ phi hPure.1 _ _ hSub) hCylinder.
have hDen:0<euclidean_unit_ball_volume R m*r^+m:=metric_ball_density_denominator_positive m hr.
have hNonnegative:(0<=(euclidean_unit_ball_volume R m*r^+m)%:E)%E:=lee_tofin (ltW hDen).
have hInverse:(0<=((euclidean_unit_ball_volume R m*r^+m)%:E)^-1)%E by rewrite inve_ge0.
have hQuotient:=@lee_wpmul2r R
  ((euclidean_unit_ball_volume R m*r^+m)%:E)^-1 hInverse _ _ hBound.
rewrite /metric_ball_density /measure_restrict.
have hAlgebra:2*84^+m*lam*euclidean_unit_ball_volume R m*r^+m=
    (2*84^+m*lam)*(euclidean_unit_ball_volume R m*r^+m) by rewrite !mulrA.
rewrite hAlgebra in hQuotient.
have hUnit:euclidean_unit_ball_volume R m*r^+m \is a GRing.unit.
  rewrite unitfE; exact:lt0r_neq0 hDen.
rewrite inver (gt_eqF hDen) -EFinM mulrK // in hQuotient.
rewrite inver (gt_eqF hDen).
exact:hQuotient.
Qed.
