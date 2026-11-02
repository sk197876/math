(** Supporting norm topology for Federer (1969), 3.1.21,
    p. 233: express closure in terms of arbitrarily small norm balls. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_closure_balls]: supporting epsilon
    characterization of Clos S in Federer 3.1.21, p. 233.
    General metric topology is used with exactly the supplied norm. *)
Lemma norm_closure_balls (R:realType) (X:lmodType R) (N:X->R)
    (hN:is_real_norm N) (S:set X) a :
  @closure (real_norm_metric_space hN) S a <->
  forall e:R,0<e -> exists x,S x /\ N (x-a)<e.
Proof.
split.
- move=>hcl e he.
  have hn:nbhs (a:real_norm_metric_space hN) [set x|mdist a x<e].
    apply: (proj2 (metricType_numDomainType.nbhs_mdistP a _)).
    by exists e.
  have [x [hx hax]]:=hcl _ hn.
  exists x; split=>//.
  by rewrite (real_seminorm_subtract hN.1).
- move=>h U hU.
  have [e he hb]:=proj1 (metricType_numDomainType.nbhs_mdistP a U) hU.
  have [x [hx hxa]]:=h e he.
  exists x; split=>//; apply: hb.
  change (N (a-x)<e).
  by rewrite (real_seminorm_subtract hN.1).
Qed.
