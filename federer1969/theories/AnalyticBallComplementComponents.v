(** Federer (1969), 3.4.8(11), p. 333:
    the original open ball outside Phi=0 has
    finitely many components once the induction gives
    local finiteness of its actual critical variety.
    The original barrier, derivative, compact ball,
    critical maxima and boundary values are proved here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP NormRegularity
  NormAnalyticUP NormAnalyticLocal FiniteNormMetricCompactness AnalyticCriticalVariety
  AnalyticComponentBarrier NormComponentBarrierBoundary AnalyticPositiveRegionComponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section BallComponents.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Variables (A:set X) (phi:X->R^o) (epsilon:R).
Local Notation psi:=(fun y=>(epsilon^+2-(NX y)^+2)*(phi y)^+2).
Local Notation K:=([set y:X|NX y<=epsilon]).

(** Source for [analytic_ball_complement_components_from_induction]:
    all noninductive steps of the full-dimensional
    component argument in 3.4.8(11), p. 333.
    Its single induction input concerns the actual
    lower-dimensional critical variety. No component-count
    conclusion or critical maximum is assumed. *)
Theorem analytic_ball_complement_components_from_induction:
  (0<n)%N ->0<epsilon ->
  @norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R) A phi ->
  K `<=` A ->
  (forall D:X->Hom X R^o,
    (forall x,A x ->has_norm_differential NX (fun z:R^o=>`|z|) A psi x (D x)) ->
    forall a,K a ->exists U:set X,@open T U /\ U a /\
      finite_set (@connected_component T [set x|A x /\ forall v,D x v = 0] @`
        ([set x|A x /\ forall v,D x v = 0] `&` U))) ->
  finite_set (@connected_component T [set x|NX x<epsilon /\ phi x<>0] @`
    [set x|NX x<epsilon /\ phi x<>0]).
Proof.
move=>hN hE hPhi hKA hInduction.
have hPsi:=@analytic_component_barrier_analytic R n A phi epsilon hPhi.
have [D [F [hD hRest]]]:=@analytic_critical_variety_exists R X NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) A psi hPsi.
have hCompact:@compact T K:=@finite_norm_metric_ball_compact R X NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) epsilon.
apply:(@analytic_positive_region_finite_components R n A
  [set x|NX x<epsilon /\ phi x<>0] K psi D hN hPsi hD hCompact _ hKA).
- move=>x [hx hNonzero];exact:ltW hx.
- move=>x [hx hNonzero];exact:analytic_component_barrier_positive hE hx hNonzero.
- move=>a ha x hClosure hNotInterior.
  exact:(@norm_component_barrier_boundary_zero R X NX hNX A phi epsilon
    (norm_class_continuous (norm_analytic_class_all_orders hPhi 0%N)) hKA a x hClosure hNotInterior).
- exact:hInduction D hD.
Qed.
End BallComponents.
