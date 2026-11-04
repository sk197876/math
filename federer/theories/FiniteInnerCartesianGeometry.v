(** Federer (1969), 3.2.47(1),(2), p. 283: supporting
    actual Cartesian inner coordinates for the product E times I.
    The two factors are identified with Euclidean spaces only
    through their public inverse and isometry laws, including
    empty coordinate blocks. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric ProductInner FiniteInnerChartUP
  EuclideanBlockCoordinates EuclideanBlockLinear EuclideanMetricProduct EuclideanCartesianMap
  LipschitzUP LipschitzBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_block_split_difference]: supporting
    linear block-coordinate identity from 2.6.5, p. 120,
    used for the actual product metric in 3.2.47, p. 283. *)
Lemma euclidean_block_split_difference (R:realType) a b (x y:R_n R (a+b)):
  euclidean_block_split (x-y)=euclidean_block_split x-euclidean_block_split y.
Proof.
apply:(can_inj (@euclidean_block_joinK R a b)).
by rewrite euclidean_block_splitK euclidean_block_join_difference !euclidean_block_splitK.
Qed.

(** Source for [finite_inner_chart_inverse_lipschitz]: actual
    orthonormal inverse coordinates are globally nonexpanding,
    supporting 3.2.47(1),(2), p. 283, by 1.7.1, p. 28. *)
Lemma finite_inner_chart_inverse_lipschitz (R:realType) (V:lmodType R)
    B (hB:@is_inner_product R V B) n
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n)) (A:set V):
  is_finite_inner_chart B e p ->
  @is_metric_lipschitz R (inner_metric_space hB)
    (inner_metric_space (@euclidean_inner_productP R n)) A p.
Proof.
move=>hChart; apply:metric_lipschitz_of_bound; split; first exact:ler01.
move=>x y _ _; rewrite !inner_metric_distanceE mul1r.
change (is_true (inner_norm (@euclidean_inner_productP R n) (p x-p y)<=inner_norm hB (x-y))).
rewrite -linearB; by rewrite (finite_inner_chart_inverse_norm hB hChart).
Qed.

(** Source for [finite_inner_cartesian_parametrization]: actual
    Cartesian parametrization through the two independent charts,
    supporting the product E times I in 3.2.47, p. 283.
    No globally selected chart is part of this definition. *)
Definition finite_inner_cartesian_parametrization (R:realType) (V W:lmodType R)
    n v (e:Hom (R_n R n) V) (f:Hom (R_n R v) W) (z:R_n R (n+v)):
    (V*W)%type:=(e (euclidean_block_split z).1,f (euclidean_block_split z).2).

(** Source for [finite_inner_cartesian_parametrization_norm]:
    exact actual Cartesian norm, by 1.7.11, p. 36,
    supporting the product transfer in 3.2.47, p. 283. *)
Lemma finite_inner_cartesian_parametrization_norm (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C) n v
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n))
    (f:Hom (R_n R v) W) (q:Hom W (R_n R v)):
  is_finite_inner_chart B e p ->is_finite_inner_chart C f q ->forall z,
  inner_norm (product_inner_productP hB hC) (finite_inner_cartesian_parametrization e f z)=
    inner_norm (@euclidean_inner_productP R (n+v)) z.
Proof.
move=>hV hW z; apply:inner_norm_value; first exact:inner_norm_nonnegative.
rewrite inner_norm_sqr product_innerE /finite_inner_cartesian_parametrization /=
  (finite_inner_chart_product hV) (finite_inner_chart_product hW).
have hSplit:=@euclidean_block_splitK R n v z.
exact (eq_trans (esym (congr2 (@euclidean_inner_product R (n+v)) hSplit hSplit))
  (@euclidean_block_join_inner R n v (euclidean_block_split z) (euclidean_block_split z))).
Qed.

(** Source for [finite_inner_cartesian_parametrization_difference]:
    the actual product parametrization is linear on differences,
    supporting the isometry used in 3.2.47, p. 283. *)
Lemma finite_inner_cartesian_parametrization_difference (R:realType) (V W:lmodType R)
    n v (e:Hom (R_n R n) V) (f:Hom (R_n R v) W) (x y:R_n R (n+v)):
  finite_inner_cartesian_parametrization e f (x-y)=
    finite_inner_cartesian_parametrization e f x-finite_inner_cartesian_parametrization e f y.
Proof.
rewrite /finite_inner_cartesian_parametrization euclidean_block_split_difference /=.
by rewrite !linearB.
Qed.

(** Source for [finite_inner_cartesian_parametrization_lipschitz]:
    actual product coordinates preserve every distance, hence are
    globally Lipschitz with constant one; supporting 3.2.47(1),(2), p. 283. *)
Lemma finite_inner_cartesian_parametrization_lipschitz (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C) n v
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n))
    (f:Hom (R_n R v) W) (q:Hom W (R_n R v)):
  is_finite_inner_chart B e p ->is_finite_inner_chart C f q ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R (n+v)))
    (inner_metric_space (product_inner_productP hB hC)) setT
    (finite_inner_cartesian_parametrization e f).
Proof.
move=>hV hW; apply:metric_lipschitz_of_bound; split; first exact:ler01.
move=>x y _ _; rewrite !inner_metric_distanceE mul1r.
change (is_true (inner_norm (product_inner_productP hB hC)
  (finite_inner_cartesian_parametrization e f x-finite_inner_cartesian_parametrization e f y)<=
  inner_norm (@euclidean_inner_productP R (n+v)) (x-y))).
rewrite -finite_inner_cartesian_parametrization_difference.
by rewrite (@finite_inner_cartesian_parametrization_norm R V W B C hB hC n v e p f q hV hW).
Qed.

(** Source for [finite_inner_cartesian_parametrization_image]:
    exact original product image, retaining arbitrary subsets and
    both zero-dimensional factors in 3.2.47(1),(2), p. 283. *)
Lemma finite_inner_cartesian_parametrization_image (R:realType) (V W:lmodType R)
    B C n v (e:Hom (R_n R n) V) (p:Hom V (R_n R n))
    (f:Hom (R_n R v) W) (q:Hom W (R_n R v)) (E:set V) (Z:set W):
  is_finite_inner_chart B e p ->is_finite_inner_chart C f q ->
  finite_inner_cartesian_parametrization e f @`
    (euclidean_cartesian_set (p @` E) (q @` Z))=[set z:V*W|E z.1 /\Z z.2].
Proof.
move=>hV hW; apply/seteqP; split=>z.
- move=>[a [[x hx hpx] [y hy hqy]] <-].
  rewrite /finite_inner_cartesian_parametrization -hpx -hqy
    (finite_inner_chart_right_inverse hV) (finite_inner_chart_right_inverse hW).
  by split.
- move=>[hx hy]; exists (euclidean_block_join (p z.1,q z.2)).
  + change ((p @` E) (euclidean_block_split (euclidean_block_join (p z.1,q z.2))).1 /\
      (q @` Z) (euclidean_block_split (euclidean_block_join (p z.1,q z.2))).2).
    rewrite euclidean_block_joinK /=.
    split; [by exists z.1|by exists z.2].
  + rewrite /finite_inner_cartesian_parametrization euclidean_block_joinK /=
      (finite_inner_chart_right_inverse hV) (finite_inner_chart_right_inverse hW).
    exact (esym (surjective_pairing z)).
Qed.
