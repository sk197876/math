(** Federer (1969), 3.3.17, pp. 300–301: each original
    uniform cone test outside the rectifiable part is null. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace EuclideanBallVolume
  StructureSmallConeCriterionUP StructureConeBoundTests StructureConeCostBounds
  StructureCone StructureProjectionKernel StructurePureConeDensity RectifiableSetUP
  EuclideanFiniteMeasureDensityOne MetricDensityOneFiniteUpperBound MeasureDerivationContext
  MeasureDerivates CenteredBallRelations PartialFunctionUP
  MetricDensities MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_pure_density_test_null]: the last
    paragraph of the proof of Federer 3.3.17, pp. 300–301.
    Actual uniform cone bounds, actual purity and original
    almost-everywhere relative density one imply nullity of the
    original test subset. These independent supporting hypotheses
    are derived in the final theorem; no nullity is supplied.
    The exact printed coefficient and infinite densities remain. *)
Theorem structure_pure_density_test_null (R:realType) n m (hmn:(m<=n)%N)
    (psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (s lam delta:R):
  is_derivation_measure psi ->psi setT< +oo ->
  is_purely_measure_m_unrectifiable psi m A ->(0<s<1)%R ->(0<=lam)%R ->(0<delta)%R ->
  A `<=` structure_density_cone_test hmn psi p s lam delta ->psi A= 0.
Proof.
move=>hPsi hFinite hPure hS hLam hDelta hSub.
have hAgreement:=@euclidean_finite_measure_restriction_density_one R n psi A hPsi hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose e:=(s/4)%R.
have hE:(0<e<1)%R by rewrite /e; have [hS0 hS1]:=andP hS; apply/andP; split; lra.
have hAperture:(4*e=s)%R by rewrite /e; lra.
have hXi:(0<delta%:E)%E by rewrite lte_fin.
have hMass x:A x ->forall r:R,(0<r)%R ->(r%:E<=delta%:E)%E ->
    psi (A `&` structure_cone (structure_projection_kernel hmn p) x r%:E (4*e))<=
      (lam*euclidean_unit_ball_volume R m*r^+m*(4*e)^+m)%:E.
  move=>hx r hr hrd; rewrite hAperture.
  have hRadius:(0<r<=delta)%R by apply/andP; split=>//; exact:hrd.
  have hCost:=(hSub x hx).1 r hRadius.
  have hBound:=(@structure_cone_cost_mass_bound R n m hmn psi setT p x r s
    (euclidean_unit_ball_volume R m*lam) hr (andP hS).1).1 hCost.
  rewrite setTI [(euclidean_unit_ball_volume R m*lam)%R]mulrC in hBound.
  apply:le_trans _ hBound.
  apply:(@measure_mono R _ psi hPure.1)=>y [_ hy]; exact:hy.
have hUpper a:=@structure_pure_cone_upper_density R n m hmn psi A p e lam delta%:E a
  hPure hE hLam hXi hMass.
have hConstant:(0<=(structure_small_cone_constant R m)%:E)%E.
  rewrite lee_fin; exact:ltW (structure_small_cone_constant_positive R m).
have hNoAgreement a:A a ->
    ~partial_function_graph (measure_derivate (measure_restrict psi A) psi
      (@centered_closed_ball_relation R [the metricType R of X])) a 1.
  move=>ha hOne.
  have hCoefficient:(0<= 2*84^+m*lam)%R.
    apply:mulr_ge0; last exact:hLam.
    apply:mulr_ge0; by rewrite ?exprn_ge0 // ler0n.
  have hTransferred:=@metric_density_one_finite_upper_bound R [the metricType R of X] m
    psi (measure_restrict psi A) a (2*84^+m*lam)%R hPsi hOne hCoefficient (hUpper a).
  have hBound:=lee_wpmul2l hConstant hTransferred.
  rewrite -EFinM structure_small_cone_coefficient_cancel in hBound.
  have hStrict:=(hSub a ha).2.
  by have:=lt_le_trans hStrict hBound; rewrite ltxx.
apply:(@measure_null_subset R [the choiceType of X] psi hPure.1 A _ _ hAgreement).
move=>a ha; split; first exact:ha.
exact:hNoAgreement a ha.
Qed.
