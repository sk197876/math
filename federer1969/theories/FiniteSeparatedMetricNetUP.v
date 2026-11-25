(** Federer (1969), 3.2.40, p. 276: supporting finite
    separated nets for actual Cantor-square tube estimates.
    Specify only inclusion, separation and covering, before
    proving existence from compactness and the earlier opaque
    maximal-separated-set interface of 2.2.16, p. 71. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals topology.
From Federer Require Import SeparatedMetricSetUP MaximalSeparatedSealed
  SeparatedMetricNet CompactSeparatedCardinality MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_finite_separated_metric_net]: supporting independent
    finite-net laws for the tube lower bound in Federer 3.2.40,
    p. 276. No mass or Minkowski-content conclusion is assumed. *)
Record is_finite_separated_metric_net (R:realType) (X:metricType R)
    (K:set X) (r:R) (B:{fset X}):Prop:={
  (** Source for [finite_metric_net_inside]: supporting centres in
      the original compact source of Federer 3.2.40, p. 276. *)
  finite_metric_net_inside:forall a,a \in B ->K a;
  (** Source for [finite_metric_net_separated]: supporting strict
      separation in Federer 3.2.40, p. 276; disjoint open
      half-radius balls are a consequence, not a premise. *)
  finite_metric_net_separated:forall a b,a \in B ->b \in B ->a!=b ->r<mdist a b;
  (** Source for [finite_metric_net_covers]: supporting covering
      by closed r-balls in Federer 3.2.40, p. 276. *)
  finite_metric_net_covers:K `<=` \bigcup_(a in [set` B]) metric_closed_ball a r
}.

(** Source for [compact_finite_separated_metric_net_exists]: supporting
    finite nets for Federer 3.2.40, p. 276. Compactness makes
    the earlier opaque maximal separated set finite; maximality
    gives the exact covering law. The local witness handles
    empty K and adds no selected global auxiliary object. *)
Theorem compact_finite_separated_metric_net_exists (R:realType) (X:metricType R)
    (x0:X) (K:set X) (r:R):
  compact K ->0<r ->exists B,is_finite_separated_metric_net K r B.
Proof.
move=>hK hr.
pose S:=@MaximalSeparated.value R X K r.
have hS:=@MaximalSeparated.laws R X K r.
have hInside:S `<=` K:=@separated_subset_inside R X K r S hS.
have hSeparate:is_strictly_separated_metric_set r S:=@separated_subset_separation R X K r S hS.
have [N [_ hBound]]:=@compact_separated_cardinal_bound R X x0 K r hK hr.
have hFinite:finite_set S.
  have hSepLe a b:S a ->S b ->a<>b ->r<=mdist a b.
    move=>ha hb hDifferent; exact:ltW (hSeparate a b ha hb hDifferent).
  exact:card_le_finite (hBound S hInside hSepLe) (@finite_finset _ (@setT 'I_N)).
pose B:=fset_set S.
have hMember (a:X):a \in B <->S a.
  rewrite /B in_fset_set //; split; [exact:set_mem|exact:mem_set].
exists B; constructor.
- move=>a ha; exact:hInside a ((hMember a).1 ha).
- move=>a b ha hb /eqP hDifferent.
  exact:hSeparate a b ((hMember a).1 ha) ((hMember b).1 hb) hDifferent.
- move=>x hx.
  have [a [ha hxa]]:=@maximal_separated_subset_covers R X K S r (ltW hr) hS x hx.
  exists a; first exact:(hMember a).2 ha.
  change (is_true (mdist a x<=r)).
  by rewrite metric_sym.
Qed.
