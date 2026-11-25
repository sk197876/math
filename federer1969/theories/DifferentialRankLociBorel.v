(** Federer (1969), 3.2.3, p. 243: Borel
    decomposition into injective and singular differentials,
    retaining only actual differentiability points. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormMetric NormDifferentialUP NormClassOneUP EuclideanJacobianRank Jacobian
  PartialFunctionUP EuclideanJacobianBorel RealMetricBackground TopologicalBorel BorelFamilyBasic
  InjectiveDifferentialPieceUP InjectiveDifferentialCover InnerOwnNormTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ordinary_differential_rank_split]: the two
    cases in Federer 3.2.3, pp. 243–244, exhaust
    the actual differentiability locus. *)
Lemma ordinary_differential_rank_split (R:realType) m n (f:R_n R m->R_n R n) a:
  norm_differentiable_at (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f a <->
    injective_differential_locus f a \/ singular_differential_locus f a.
Proof.
split.
- move=>[D hD]; case:(pselect (injective D))=>hInj.
  + left; by exists D.
  + right; by exists D.
- move=>[[D [hD _]]|[D [hD _]]]; by exists D.
Qed.

(** Source for [injective_differential_locus_borel]: the
    first case of Federer 3.2.3, p. 243, is
    Borel by the exact countable cover of 3.2.2. *)
Lemma injective_differential_locus_borel (R:realType) m n (f:R_n R m->R_n R n):
  norm_class_zero (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
    (injective_differential_locus f).
Proof.
move=>hf; have [G hG]:=injective_differential_borel_cover_exists hf (ltr1n R 2).
rewrite -hG.2.1; apply:borel_set_countable_union; first exact hG.1.
move=>E hE.
exact ((inner_own_norm_borel_iff (@euclidean_inner_productP R m) E).2 (hG.2.2 E hE).1).
Qed.

(** Source for [singular_differential_locus_borel]: the
    second case of Federer 3.2.3, p. 243, is
    the Borel preimage of zero under the exact partial
    top-source Jacobian. *)
Lemma singular_differential_locus_borel (R:realType) m n (f:R_n R m->R_n R n):
  norm_class_zero (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
    (singular_differential_locus f).
Proof.
move=>hf.
have hZero:borel_set [set (0:real_line_metric R)].
  apply:closed_borel_set; apply:accessible_closed_set1; apply:hausdorff_accessible; exact:metric_hausdorff.
have hPre:=euclidean_top_jacobian_borel_preimage hf hZero.
have he:partial_function_preimage (euclidean_jacobian m setT f) [set (0:real_line_metric R)]=
    singular_differential_locus f.
  apply/seteqP; split=>a.
  - move=>[j [hj hz]]; change (j=0) in hz; subst j; exact ((singular_differential_locus_jacobian f a).2 hj).
  - move=>ha; exists 0; split; first exact ((singular_differential_locus_jacobian f a).1 ha).
    by [].
rewrite he in hPre.
exact ((inner_own_norm_borel_iff (@euclidean_inner_productP R m) _).2 hPre).
Qed.

(** Source for [ordinary_differential_locus_borel]: the
    Borel differentiability reduction in Federer 3.2.3,
    p. 243, through 3.1.1 and Rademacher. *)
Lemma ordinary_differential_locus_borel (R:realType) m n (f:R_n R m->R_n R n):
  norm_class_zero (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
    [set a|norm_differentiable_at (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT f a].
Proof.
move=>hf.
have he:[set a|norm_differentiable_at (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f a]=
    injective_differential_locus f `|` singular_differential_locus f.
  apply/seteqP; split=>a.
  - exact (ordinary_differential_rank_split f a).1.
  - exact (ordinary_differential_rank_split f a).2.
rewrite he; exact (borel_family_binary_union (borel_sets_family _)
  (injective_differential_locus_borel hf) (singular_differential_locus_borel hf)).
Qed.
