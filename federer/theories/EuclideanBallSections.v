(** Federer (1969), 2.10.27, pp. 190–191: closed Euclidean ball sections
    used for the sharp spherical comparison. Prove the actual
    squared-distance section formula, including boundary sections of radius
    zero. The scan on p. 191 writes the projection as the open ball B(u,r);
    the closed-ball projection is B[u,r]. The working erratum has no p. 191
    entry; this is a local correction, separate from Federer's erratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  InnerNormedTopology EuclideanBlockCoordinates EuclideanBallVolume EuclideanMetricProduct MetricCartesianProductUP MetricClosedBalls CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_block_pair_squared_distance]: supporting
    ball-section metric identity in 2.10.27,
    pp. 190–191, for actual Euclidean block pairs. *)
Lemma euclidean_block_pair_squared_distance (R : realType) m n
    (u y : inner_metric_space (@euclidean_inner_productP R m))
    (v z : inner_metric_space (@euclidean_inner_productP R n)) :
  mdist (@euclidean_block_join R m n (u,v)) (euclidean_block_join (y,z))^+2=
    mdist u y^+2+mdist v z^+2.
Proof.
by rewrite (@euclidean_block_squared_distance R m n) !euclidean_block_joinK.
Qed.

(** Source for [euclidean_closed_ball_section]: direct
    closed-ball section formula in 2.10.27,
    p. 190. Keep boundary y with distance r;
    its section has radius zero rather than being
    omitted as in the printed open-projection identity. *)
Theorem euclidean_closed_ball_section (R : realType) m n
    (u y : inner_metric_space (@euclidean_inner_productP R m))
    (v : inner_metric_space (@euclidean_inner_productP R n)) (r : R) :
  0<=r -> mdist u y<=r ->
  metric_product_section (fun a b=>@euclidean_block_join R m n (a,b))
    (metric_closed_ball (euclidean_block_join (u,v)) r) y=
    metric_closed_ball v (Num.sqrt (r^+2-mdist u y^+2)).
Proof.
move=> hr hy.
have hd0 : 0<=r^+2-mdist u y^+2.
  rewrite subr_ge0 (ler_sqr _ _)=> //; by rewrite nnegrE ?mdist_ge0.
apply/seteqP; split=> z hz.
- have hz' : mdist (euclidean_block_join (u,v)) (euclidean_block_join (y,z))<=r := hz.
  have hz2 : mdist (euclidean_block_join (u,v)) (euclidean_block_join (y,z))^+2<=r^+2.
    rewrite (ler_sqr _ _)=> //; by rewrite nnegrE ?mdist_ge0.
  rewrite euclidean_block_pair_squared_distance in hz2.
  change (is_true (mdist v z<=Num.sqrt (r^+2-mdist u y^+2))).
  rewrite -(ler_sqr _ _) ?nnegrE ?mdist_ge0 ?sqrtr_ge0 // sqr_sqrtr //.
  lra.
- have hz' : mdist v z<=Num.sqrt (r^+2-mdist u y^+2) := hz.
  have hz2 : mdist v z^+2<=r^+2-mdist u y^+2.
    rewrite -(sqr_sqrtr hd0) (ler_sqr _ _)=> //; by rewrite nnegrE ?mdist_ge0 ?sqrtr_ge0.
  change (is_true (mdist (euclidean_block_join (u,v)) (euclidean_block_join (y,z))<=r)).
  rewrite -(ler_sqr _ _) ?nnegrE ?mdist_ge0 // euclidean_block_pair_squared_distance.
  lra.
Qed.

(** Source for [euclidean_closed_ball_first_projection]: local
    correction to the printed fB[(u,v),r]=B(u,r)
    in 2.10.27, p. 191. The projection is
    the closed ball B[u,r]. Every point of that
    ball is attained using the fixed second centre v. *)
Theorem euclidean_closed_ball_first_projection (R : realType) m n
    (u : inner_metric_space (@euclidean_inner_productP R m))
    (v : inner_metric_space (@euclidean_inner_productP R n)) (r : R) :
  0<=r ->
  (fun p=>(@euclidean_block_split R m n p).1) @`
    (metric_closed_ball (euclidean_block_join (u,v)) r)=metric_closed_ball u r.
Proof.
move=> hr; apply/seteqP; split.
- move=> y [p hp <-].
  have hh := (metric_product_first_nonexpanding (euclidean_blocks_are_metric_product R m n)).2
    (euclidean_block_join (u,v)) p Logic.I Logic.I.
  rewrite mul1r euclidean_block_joinK /= in hh; exact: le_trans hh hp.
- move=> y hy; exists (euclidean_block_join (y,v)); last by rewrite euclidean_block_joinK.
  change (is_true (mdist (euclidean_block_join (u,v)) (euclidean_block_join (y,v))<=r)).
  rewrite -(ler_sqr _ _) ?nnegrE ?mdist_ge0 // euclidean_block_pair_squared_distance mdistxx expr0n /= addr0.
  rewrite (ler_sqr _ _)=> //; by rewrite nnegrE ?mdist_ge0.
Qed.

(** Source for [closed_ball_projection_open_ball_counterexample]:
    local boundary counterexample to the printed open
    projection in 2.10.27, p. 191. The
    projection of the closed Euclidean unit ball
    contains a point at distance exactly one; the
    open unit ball does not. Both factors have
    positive dimension. This is not an erratum entry. *)
Theorem closed_ball_projection_open_ball_counterexample (R : realType) :
  (fun p=>(@euclidean_block_split R 1 1 p).1) @`
    (metric_closed_ball (euclidean_block_join
      ((0 : inner_metric_space (@euclidean_inner_productP R 1)),
       (0 : inner_metric_space (@euclidean_inner_productP R 1)))) 1)<>
    metric_open_ball (0 : inner_metric_space (@euclidean_inner_productP R 1)) 1.
Proof.
move=> he.
rewrite (@euclidean_closed_ball_first_projection R 1 1 0 0 1 ler01) in he.
pose y : inner_metric_space (@euclidean_inner_productP R 1) := [ffun _=>1%R].
have hd : mdist (0 : inner_metric_space (@euclidean_inner_productP R 1)) y = 1.
  by rewrite inner_metric_normE subr0 euclidean_norm_one /y ffunE normr1.
have hclosed : metric_closed_ball (0 : inner_metric_space (@euclidean_inner_productP R 1)) 1 y.
  by rewrite /metric_closed_ball /= hd.
have hopen : metric_open_ball (0 : inner_metric_space (@euclidean_inner_productP R 1)) 1 y by rewrite -he.
by rewrite /metric_open_ball /= hd ltxx in hopen.
Qed.
