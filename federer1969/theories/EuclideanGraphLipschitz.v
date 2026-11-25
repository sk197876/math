(** Federer (1969), 3.2.3, p. 244: the graph
    map has Lipschitz bound M+epsilon and its scaled
    identity block supplies a positive lower expansion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerNormInequalities
  EuclideanBlockLinearMaps EuclideanBlockNorms EuclideanMetricProduct MetricCartesianProductUP
  EuclideanGraphLift InnerMetric LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_graph_increment_norm_bound]:
    Lip(g)<=Lip(f)+epsilon in Federer 3.2.3,
    p. 244, before inserting the bound for f.
    Both increments use their actual original values. *)
Lemma euclidean_graph_increment_norm_bound (R:realType) m n
    (f:R_n R m->R_n R n) e x y:
  inner_norm (@euclidean_inner_productP R (n+m))
    (euclidean_graph_lift f e x-euclidean_graph_lift f e y)<=
  inner_norm (@euclidean_inner_productP R n) (f x-f y)+
    `|e|*inner_norm (@euclidean_inner_productP R m) (x-y).
Proof.
pose I:=@euclidean_first_injection_map R n m.
pose K:=@euclidean_last_injection_map R n m.
have hDiff:euclidean_graph_lift f e x-euclidean_graph_lift f e y=
    I (f x-f y)+e*:K (x-y).
  rewrite /euclidean_graph_lift.
  change (I (f x)+e*:K x-(I (f y)+e*:K y)=I (f x-f y)+e*:K (x-y)).
  rewrite !linearB /=.
  rewrite !opprD ?scalerN.
  exact (addrACA (I (f x)) (e*:K x) (-I (f y)) (-(e*:K y))).
rewrite hDiff.
apply:le_trans (inner_norm_triangle (@euclidean_inner_productP R (n+m)) _ _) _.
rewrite inner_normZ.
change (inner_norm (@euclidean_inner_productP R (n+m)) (@euclidean_first_injection R n m (f x-f y))+
  `|e|*inner_norm (@euclidean_inner_productP R (n+m)) (@euclidean_last_injection R n m (x-y))<=
  inner_norm (@euclidean_inner_productP R n) (f x-f y)+`|e|*inner_norm (@euclidean_inner_productP R m) (x-y)).
by rewrite euclidean_first_injection_norm euclidean_last_injection_norm.
Qed.

(** Source for [euclidean_graph_lipschitz_bound]: the
    graph map's finite bound in Federer 3.2.3,
    p. 244, with an explicit bound M for f.
    Coefficient zero and empty blocks remain covered. *)
Lemma euclidean_graph_lipschitz_bound (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (e M:R):
  0<=e -> is_metric_lipschitz_bound setT f M ->
  @is_metric_lipschitz_bound R [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R (n+m))] setT (euclidean_graph_lift f e) (M+e).
Proof.
move=>he hM; split; first exact:addr_ge0 hM.1 he.
move=>x y _ _; rewrite !inner_metric_distanceE.
apply:le_trans (euclidean_graph_increment_norm_bound f e x y) _.
rewrite (ger0_norm he) mulrDl.
have hh:=hM.2 x y Logic.I Logic.I; rewrite !inner_metric_distanceE in hh.
exact (lerD hh (lexx _)).
Qed.

(** Source for [euclidean_linear_graph_lower_bound]: the
    scaled source block used for univalence in Federer
    3.2.3, p. 244, also gives a norm lower bound
    through the nonexpanding second projection. *)
Lemma euclidean_linear_graph_lower_bound (R:realType) m n
    (L:Hom (R_n R m) (R_n R n)) e v:
  `|e|*inner_norm (@euclidean_inner_productP R m) v<=
    inner_norm (@euclidean_inner_productP R (n+m)) (euclidean_linear_graph_lift L e v).
Proof.
pose G:=euclidean_linear_graph_lift L e.
pose Q:=@euclidean_last_block_map R n m.
have hQ:=metric_product_second_nonexpanding (@euclidean_blocks_are_metric_product R n m).
have hh:=hQ.2 (G v) 0 Logic.I Logic.I.
change (is_true (inner_norm (@euclidean_inner_productP R m) (Q (G v)-Q 0)<=
  1*inner_norm (@euclidean_inner_productP R (n+m)) (G v-0))) in hh.
rewrite linear0 !subr0 mul1r /G euclidean_linear_graph_liftE euclidean_graph_lift_last inner_normZ in hh.
exact hh.
Qed.
