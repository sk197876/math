(** Federer (1969), 3.2.13, p. 250: continuity
    of the scalar Gamma integrand follows from the actual
    internal differential. This adapter identifies the scalar
    epsilon law with the existing real-line topology. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom RealNormUP RealMetricBackground NormDifferentialUP NormDifferentialLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_differential_continuous_at]: the
    continuity consequence of 3.1.1 used for Gamma's
    integrand in Federer 3.2.13, p. 250.
    Uses the project's epsilon derivative and metric-neighbourhood laws. *)
Lemma scalar_differential_continuous_at (R:realType) (f:R->R) a (L:Hom R^o R^o):
  has_norm_differential (fun r:R^o=>`|r|) (fun r:R^o=>`|r|) setT f a L ->
  (fun x:real_line_metric R=>(f x:real_line_metric R)) @ a -->(f a:real_line_metric R).
Proof.
move=>hD U hU.
have [e he hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (f a:real_line_metric R) U) hU.
have [d [hd hBound]]:=norm_differential_continuous_at (@scalar_absolute_value_norm R) hD he.
apply:(proj2 (metricType_numDomainType.nbhs_mdistP (a:real_line_metric R) _)).
exists d; first exact hd.
move=>x hx; apply:hBall.
change (`|f a-f x|<e).
have hSmall:`|x-a|<d by rewrite -[x-a]opprB normrN; exact hx.
have h:=hBound (x-a) Logic.I hSmall.
rewrite [a+(x-a)]addrC subrK in h.
rewrite -[f a-f x]opprB normrN; exact h.
Qed.
