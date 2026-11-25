(** Federer (1969), 3.4.12, pp. 338–339:
    completeness of the original complex Banach spaces
    is independent of their isometric coordinates. This
    missing transport connection reuses the existing Cauchy-image
    theorem and actual metric neighbourhoods of 2.2.8, p. 64. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompleteMetricUP MetricCauchyImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [complete_metric_isometric_bijection]: transport
    the original completeness law through an actual isometric
    bijection, supporting 3.4.12, pp. 338–339.
    Both inverse equations and all distances must be proved. *)
Theorem complete_metric_isometric_bijection (R:realType) (X Y:metricType R)
    (f:X->Y) (g:Y->X):
  cancel f g ->cancel g f ->
  (forall x y,mdist (f x) (f y)=mdist x y) ->
  is_complete_metric_space Y ->is_complete_metric_space X.
Proof.
move=>hLeft hRight hDistance hComplete F PF hCauchy.
have PF':ProperFilter (f @ F):=@fmap_proper_filter X Y f F PF.
have hNon x y:mdist (f x) (f y)<=mdist x y by rewrite hDistance.
have hImage:=@distance_nonincreasing_cauchy_image R X Y f F PF hNon hCauchy.
have [y hy]:=hComplete (f @ F) PF' hImage.
exists (g y)=>U hU.
have [e he hSub]:=(metricType_numDomainType.nbhs_mdistP (g y) U).1 hU.
have hNeighbourhood:nbhs y [set v:Y|mdist y v<e].
  apply:(metricType_numDomainType.nbhs_mdistP y _).2;exists e=>//v hv;exact:hv.
have hBall:=hy _ hNeighbourhood.
apply:(@filterS X F (@filter_filter X F PF) _ _ _ hBall)=>x hx.
apply:hSub.
change (is_true (mdist (g y) x<e)).
rewrite -(hDistance (g y) x) hRight;exact:hx.
Qed.
