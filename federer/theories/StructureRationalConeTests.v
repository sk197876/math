(** Federer (1969), 3.3.17, p. 300: actual countable
    rational tests cover every original uniform cone test. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace EuclideanProjectionMetric
  EuclideanBallVolume StructureSmallConeCriterionUP StructureConeBoundTests StructureNearbyProjectionCones
  RationalApertureRefinement StructureCone StructureProjectionKernel StructureConeCostBounds
  MetricClosedBalls MetricDensities ExtendedRealOrderTopology MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_rational_cone_test_refinement]: the
    countable-subfamily assertion in Federer 3.3.17, p. 300.
    Choose rational mu above original lambda and below c*Theta*,
    rational 0<t<s with lambda*s^m<mu*t^m, an actual q in the
    original dense projection set with distance less than s-t,
    and a rational positive smaller cutoff. The proved original
    cone inclusion and normalized mass inequalities then give
    the original B(q,t,mu,epsilon). All choices stay local. *)
Theorem structure_rational_cone_test_refinement (R:realType) n m (hmn:(m<=n)%N)
    (psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (D:set (orthogonal_projection_metric_space R n m))
    (p:orthogonal_projection_metric_space R n m)
    (a:inner_metric_space (@euclidean_inner_productP R n)) (s lam delta:R):
  is_measure psi ->dense D ->(0<s<1)%R ->(0<lam)%R ->(0<delta)%R ->
  structure_density_cone_test hmn psi p s lam delta a ->
  exists (q:orthogonal_projection_metric_space R n m) (t mu epsilon:rat),
    D q /\(0<(ratr t:R)<1)%R /\(0<(ratr mu:R))%R /\(0<(ratr epsilon:R))%R /\
    structure_density_cone_test hmn psi q (ratr t) (ratr mu) (ratr epsilon) a.
Proof.
move=>hPsi hDense hS hLam hDelta hTest.
have [mu [hLamMu hMuDensity]]:=@extended_rationals_order_dense R _ _ hTest.2.
have hLamMuR:(lam<(ratr mu:R))%R:=hLamMu.
have hMu:(0<(ratr mu:R))%R:=lt_trans hLam hLamMuR.
have [t [hT hPower]]:=@rational_aperture_refinement R m s lam (ratr mu) (andP hS).1 hLamMuR.
have [hT0 hTS]:=andP hT.
have hT1:((ratr t:R)<1)%R:=lt_trans hTS (andP hS).2.
have hGap:(0<s-ratr t)%R by rewrite subr_gt0.
pose P:=orthogonal_projection_metric_space R n m.
have hNonempty:[set q:P|(mdist p q<s-ratr t)%R] !=set0.
  exists p; change (is_true (mdist p p<s-ratr t)%R).
  by rewrite mdistxx.
have [q [hDistance hQ]]:=hDense _ hNonempty (metric_open_ball_open p (s-ratr t)%R).
have [epsilon /andP[hEpsilon hEpsilonDelta]]:=rat_in_itvoo hDelta.
exists q,t,mu,epsilon; split; first exact:hQ.
split; first by apply/andP; split.
split; first exact:hMu.
split; first exact:hEpsilon.
split; last exact:hMuDensity.
move=>r /andP[hr hrEpsilon].
have hrDelta:(r<=delta)%R:=le_trans hrEpsilon (ltW hEpsilonDelta).
have hRadius:(0<r<=delta)%R by apply/andP; split.
have hOldCost:=hTest.1 r hRadius.
have hOldMass:=(@structure_cone_cost_mass_bound R n m hmn psi setT p a r s
  (euclidean_unit_ball_volume R m*lam) hr (andP hS).1).1 hOldCost.
apply:(@structure_cone_cost_mass_bound R n m hmn psi setT q a r (ratr t)
  (euclidean_unit_ball_volume R m*ratr mu) hr hT0).2.
rewrite setTI in hOldMass.
rewrite setTI.
have hCone:=@structure_nearby_projection_cone_subset R n m hmn p q a r%:E s (ratr t)
  hT0 hTS hDistance.
have hMono:=@measure_mono R _ psi hPsi _ _ hCone.
refine (le_trans hMono _).
apply:le_trans hOldMass _.
rewrite lee_fin.
pose alpha:=euclidean_unit_ball_volume R m.
have hFactor:(0<=alpha*r^+m)%R.
  apply:mulr_ge0; [exact:ltW ((euclidean_unit_ball_volumeE R m).2)|apply:exprn_ge0; exact:ltW hr].
have hScaled:=ler_wpM2l hFactor (ltW hPower).
have hLeft:(alpha*r^+m*(lam*s^+m)=alpha*lam*r^+m*s^+m)%R by nra.
have hRight:(alpha*r^+m*(ratr mu*(ratr t)^+m)=alpha*ratr mu*r^+m*(ratr t)^+m)%R by nra.
rewrite hLeft hRight in hScaled.
exact:hScaled.
Qed.

(** Source for [structure_countable_cone_tests]: the original
    countable union of B(q,t,mu,epsilon) in Federer 3.3.17,
    p. 300. D is supplied only as an independent local parameter
    family; the final theorem proves its actual countable density.
    Apertures, bounds and cutoffs use all eligible rational codes. *)
Definition structure_countable_cone_tests (R:realType) n m (hmn:(m<=n)%N)
    (psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (D:set (orthogonal_projection_metric_space R n m)):=
  \bigcup_(q in D) \bigcup_(t in [set t:rat|(0<(ratr t:R)<1)%R])
    \bigcup_(mu in [set mu:rat|(0<(ratr mu:R))%R])
      \bigcup_(epsilon in [set epsilon:rat|(0<(ratr epsilon:R))%R])
        structure_density_cone_test hmn psi q (ratr t) (ratr mu) (ratr epsilon).

(** Source for [structure_local_test_in_countable_union]:
    the original union equality in Federer 3.3.17, p. 300,
    in the covering direction used by its proof. The actual
    rational refinement supplies a code in the original union. *)
Lemma structure_local_test_in_countable_union (R:realType) n m (hmn:(m<=n)%N)
    (psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (D:set (orthogonal_projection_metric_space R n m))
    (p:orthogonal_projection_metric_space R n m)
    (a:inner_metric_space (@euclidean_inner_productP R n)) (s lam delta:R):
  is_measure psi ->dense D ->(0<s<1)%R ->(0<lam)%R ->(0<delta)%R ->
  structure_density_cone_test hmn psi p s lam delta a ->
  structure_countable_cone_tests hmn psi D a.
Proof.
move=>hPsi hDense hS hLam hDelta hTest.
have [q [t [mu [epsilon [hQ [hT [hMu [hE hMember]]]]]]]]:=
  @structure_rational_cone_test_refinement R n m hmn psi D p a s lam delta hPsi hDense hS hLam hDelta hTest.
exists q; first exact:hQ.
exists t; first exact:hT.
exists mu; first exact:hMu.
by exists epsilon.
Qed.
