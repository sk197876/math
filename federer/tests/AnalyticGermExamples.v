(** Federer (1969), 3.4.5, pp. 319–321: three actual
    regressions retain the zero-dimensional unit germ, an
    actual proper line variety, and the closed locally analytic
    surface with no global defining equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology.
From Federer Require Import RealNormUP NormOpenDomainLaws NormMetric GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness LinearBasis NormAnalyticUP NormAnalyticDomain ScalarAffineAnalytic
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRingLaws AnalyticGermRing AnalyticGermMetric
  AnalyticGermGrowthUP AnalyticGermGrowthSealed AnalyticGermGrowthCover AnalyticGermGrowthCompact
  FiniteAnalyticVarietyUP AnalyticVarietyGermUP CartanSurfaceUP CartanSurfaceSealed CartanSurfaceGeometry
  CartanSurfaceLocalAnalytic CartanGlobalAnalyticRigidity CartanLocalGlobalCounterexample.
From Federer Require Import
  AnalyticEmptyGermBoundary
  AnalyticGermAddContinuity
  AnalyticGermDomain
  AnalyticGermGrowthClosed
  AnalyticGermMultiplyContinuity
  AnalyticGermNegateContinuity
  AnalyticGermSeparable
  AnalyticIrreducibleProperPrime
  AnalyticPullbackComposition
  AnalyticPullbackContinuity
  AnalyticVarietyGermRecovery
  CommutativeIdealSealed
  FiniteAnalyticBooleanNormalForm
  FunctionalAnalyticFullDimension
  NoetherianIrreducibleComponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_dimensional_unit_germ_regression]: the
    actual nonzero unit germ in R^0 lies in a compact
    positive factorial-growth class and has positive distance
    from zero in the exact metric, testing 3.4.5, p. 319. *)
Example zero_dimensional_unit_germ_regression (R:realType):
  let hN:=inner_norm_real_norm (@euclidean_inner_productP R 0) in
  let one:=@analytic_germ_one R (R_n R 0) _ hN 0 in
  let zero:=@analytic_germ_zero R (R_n R 0) _ hN 0 in
  exists s t:nat,(0<s)%N /\(0<t)%N /\
    @compact (@analytic_germ_metric R (R_n R 0) _ hN 0)
      (@AnalyticGermGrowth.value R (R_n R 0) _ hN 0 s t) /\
    @AnalyticGermGrowth.value R (R_n R 0) _ hN 0 s t one /\
    one!=zero /\0<@analytic_germ_distance R (R_n R 0) _ hN 0 one zero.
Proof.
move=>hN one zero.
have [s [t [hs [ht hOne]]]]:=@analytic_germ_positive_growth_cover R (R_n R 0) _ hN 0 one.
exists s,t;split;first exact:hs.
split;first exact:ht.
split;first exact:(@analytic_germ_growth_class_compact R (R_n R 0) _ hN 0 0
  (@coordinate_basis R 0) (@coordinate_basisP R 0) s t).
split;first exact:hOne.
have hDistinct:one!=zero:=@analytic_germ_one_not_zero R (R_n R 0) _ hN 0.
split;first exact:hDistinct.
by rewrite -analytic_germ_metric_distanceE mdist_gt0.
Qed.

(** Source for [proper_line_analytic_variety_regression]: the
    actual identity equation on the full real line defines
    precisely its nonempty proper origin variety, testing
    original domains and equations in 3.4.5, p. 320. *)
Example proper_line_analytic_variety_regression (R:realType):
  is_finite_analytic_variety (@scalar_absolute_value_norm R) setT [set x:R^o|x=0] /\
    [set x:R^o|x=0] 0 /\~[set x:R^o|x=0] 1.
Proof.
split.
- split;first exact:openT.
  exists (Finite.clone unit _),(fun (_:unit) (x:R)=>x);split.
  + move=>i a _;have hh:=@scalar_affine_analytic_at R 1 0 a.
    apply:(norm_analytic_at_domain_agreement _ hh)=>x _;by rewrite mul1r addr0.
  + move=>x;split.
    * move=>hx;split;first exact:Logic.I;by move=>i.
    * move=>[_ h];exact:h tt.
- split;first by [].
  by move/eqP;rewrite oner_eq0.
Qed.

(** Source for [closed_local_non_global_analytic_regression]: the
    same actual opaque surface is closed, proper and locally
    analytic in R^3, has no finite global analytic equations,
    and forces every actual global vanishing function to be
    identically zero, testing the converse failure in
    3.4.5, p. 321. *)
Example closed_local_non_global_analytic_regression (R:realType):
  let hN:=inner_norm_real_norm (@euclidean_inner_productP R 3) in
  @closed (real_norm_metric_space hN) (@CartanSurface.set R) /\
  (exists v:R_n R 3,~CartanSurface.set v) /\
  is_analytic_set_in hN setT (@CartanSurface.set R) /\
  ~is_finite_analytic_variety hN setT (@CartanSurface.set R) /\
  forall f:R_n R 3->R,
    @norm_analytic R (R_n R 3) R^o (inner_norm (@euclidean_inner_productP R 3))
      (fun t=>`|t|) hN (@scalar_absolute_value_norm R) setT f ->
    (forall v,CartanSurface.set v ->f v=0) ->forall v,f v=0.
Proof.
move=>hN.
have [hClosed [hProper hAnalytic]]:=@cartan_surface_closed_proper_locally_analytic R.
split;first exact:hClosed.
split;first exact:hProper.
split;first exact:hAnalytic.
split;first exact:cartan_surface_not_global_variety.
exact:cartan_global_analytic_vanisher_zero.
Qed.
