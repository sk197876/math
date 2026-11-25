(** Federer (1969), 4.1.23, p. 380:
    finite Borel cells of small diameter give
    atomic zero-current approximants. Reuse the
    tagged compact partitions from 4.1.2, p. 348;
    a half-radius choice gives the literal
    pairwise diameter bound in the source. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric
  FiniteTaggedBorelPartitionUP FiniteTaggedBorelPartitionExistence
  MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_tagged_partition_pair_distance]:
    the diameter bound on each B_k in
    Federer 4.1.23, p. 380, follows
    from two distances to its actual tag.
    Empty cells require no chosen member. *)
Lemma finite_tagged_partition_pair_distance
    (R:realType) (X:metricType R) (K:set X) (e:R)
    (I:finType) (A:I->set X) (tag:I->X)
    (hP:is_finite_tagged_borel_partition K e A tag)
    i x y:
  A i x->A i y->mdist x y<=2*e.
Proof.
move=>hx hy.
have hX:=finite_tagged_partition_mesh hP hx.
have hY:=finite_tagged_partition_mesh hP hy.
have hTriangle:=metric_triangle x (tag i) y.
rewrite (metric_sym (tag i) y) in hTriangle;lra.
Qed.

(** Source for [compact_tagged_partition_diameter_exists]:
    the original compact box B admits a finite
    Borel partition with diam(B_k)<=e,
    Federer 4.1.23, p. 380.
    The existing existence theorem also retains
    empty B and dimension zero. *)
Theorem compact_tagged_partition_diameter_exists
    (R:realType) n
    (K:set (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))))
    (e:R):
  compact K->0<e->
  exists q (A:'I_q->set (R_n R n)) (tag:'I_q->R_n R n),
    is_finite_tagged_borel_partition K (e/2) A tag /\
    forall i,(@extended_metric_diameter R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (A i)<=e%:E)%E.
Proof.
move=>hK he.
have he2:0<e/2 by rewrite divr_gt0 // ltr0n.
have[q [A [tag hP]]]:=
  finite_tagged_compact_borel_partition_exists hK he2.
exists q,A,tag;split;first exact:hP.
move=>i;apply:(metric_diameter_least
  (@extended_metric_diameter_specification R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (A i))).
- by rewrite lee_fin;exact:ltW he.
- move=>x y hx hy;rewrite lee_fin.
  have h:=finite_tagged_partition_pair_distance hP hx hy;lra.
Qed.
