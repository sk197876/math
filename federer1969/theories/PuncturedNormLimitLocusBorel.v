(** Federer (1969), 4.1.2, p. 347: measurability of the
    actual coordinate-derivative domain for continuous Banach-valued
    fields. Cauchy bounds are countable unions and intersections of
    closed sets; the innermost intersection may be arbitrary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology lra.
From Federer Require Import RealNormUP NormMetric NormedCurveDerivativeUP CompleteMetricUP
  RealMetricBackground NormMetricSubtractContinuity TopologicalProductMaps MetricClosedBalls
  TopologicalBorel ExtendedRealReciprocalBounds PuncturedNormCauchy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PuncturedNormLimitLocusBorel.
Variable R:realType.
Variable X:topologicalType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable q:X->R->Y.
Hypothesis hQ:forall t,continuous (fun x:X=>(q x t:real_norm_metric_space hNY)).
Local Notation eps := (fun m:nat=>((m.+1)%:R:R)^-1).

(** Source for [punctured_norm_limit_locus_borel]: the actual
    derivative-existence set is Borel, supporting Fubini in the
    reflexive locally Lipschitz case of Federer 4.1.2, p. 347.
    The proof retains the full two-sided norm limit. *)
Theorem punctured_norm_limit_locus_borel:
  borel_set [set x:X|exists v:Y,punctured_norm_limit NY (q x) v].
Proof.
pose H k:set (R*R):=[set p|0<`|p.1|<eps k /\0<`|p.2|<eps k].
pose C (m k:nat):set X:=\bigcap_(p in H k) [set x|NY (q x p.1-q x p.2)<=eps m].
have hClosed m k:closed (C m k).
  rewrite /C; apply:closed_bigI.
  move=>[h t] hht.
  have hPair:=topological_pair_continuous (@hQ h) (@hQ t).
  have hDiff:continuous (fun x:X=>(q x h-q x t:real_norm_metric_space hNY)).
    move=>x; exact:(continuous_comp (hPair x) (@real_norm_metric_subtract_continuous R Y NY hNY (q x h,q x t))).
  have hEq:[set x:X|NY (q x h-q x t)<=eps m]=
      (fun x:X=>(q x h-q x t:real_norm_metric_space hNY)) @^-1`
        (@metric_closed_ball R (real_norm_metric_space hNY) 0 (eps m)).
    apply/funext=>x; apply:propext.
    change (NY (q x h-q x t)<=eps m <->NY (0-(q x h-q x t))<=eps m).
    by rewrite sub0r (real_seminorm_negate hNY.1).
  rewrite hEq; apply:((@continuous_closedP X
    [the topologicalType of real_norm_metric_space hNY] _).1 hDiff).
  exact:metric_closed_ball_closed.
have hEq:[set x:X|exists v:Y,punctured_norm_limit NY (q x) v]=
    \bigcap_m \bigcup_k C m k.
  apply/funext=>x; apply:propext; split.
  - move=>[v hv] m _.
    have hEps:0<eps m by rewrite invr_gt0 ltr0n.
    have hHalf:0<eps m/2 by rewrite divr_gt0 // ltr0n.
    have[d [hd hBound]]:=hv (eps m/2) hHalf.
    have[k hk]:=positive_reciprocal_nat_small hd.
    exists k; first exact Logic.I.
    move=>[h t] [hh ht].
    have hhD:0<`|h|<d.
      apply/andP; split; first exact:(andP hh).1.
      exact:lt_trans (andP hh).2 hk.
    have htD:0<`|t|<d.
      apply/andP; split; first exact:(andP ht).1.
      exact:lt_trans (andP ht).2 hk.
    have h1:=hBound h hhD.
    have h2:NY (v-q x t)<eps m/2.
      rewrite (real_seminorm_subtract hNY.1); exact:hBound t htD.
    have hTriangle:=real_seminorm_triangle hNY.1 (q x h-v) (v-q x t).
    rewrite addrA subrK in hTriangle.
    have hSum:NY (q x h-v)+NY (v-q x t)<eps m.
      by have:=ltrD h1 h2; rewrite -splitr.
    exact:(ltW (le_lt_trans hTriangle hSum)).
  - move=>hx; apply:(@punctured_norm_cauchy_limit R Y NY hNY hY (q x))=>eta hEta.
    have[m hm]:=positive_reciprocal_nat_small hEta.
    have[k _ hC]:=hx m Logic.I.
    exists (eps k); split; first by rewrite invr_gt0 ltr0n.
    move=>h t hh ht; apply:le_lt_trans _ hm.
    exact:(hC (h,t) (conj hh ht)).
rewrite hEq.
apply:borel_set_countable_intersection (countableP setT) _ _.
- by exists 0%N.
- move=>m _; apply:borel_set_countable_union (countableP setT) _=>k _.
  exact:closed_borel_set (hClosed m k).
Qed.
End PuncturedNormLimitLocusBorel.
