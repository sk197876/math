(** Federer (1969), 3.1.21, p. 234: differentials of
    diffeomorphisms meet the linear embedding hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP TangentEmbeddingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_linear_left_inverse_lower_bound]: supporting
    application of the tangent-image equality to diffeomorphisms
    in Federer 3.1.21, p. 234. A bounded left inverse
    supplies a positive lower bound; it is not assumed for
    arbitrary closed-range embeddings. *)
Lemma norm_linear_left_inverse_lower_bound (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNY:is_real_norm NY) (L:Hom X Y) (M:Hom Y X) :
  norm_bounded_linear NY NX M -> cancel L M -> norm_linear_lower_bound NX NY L.
Proof.
move=>[C [hC hb]] hML.
have hp:0<C+1 by lra.
exists (1/(C+1)); split; first by rewrite divr_gt0.
move=>x.
have hh:=hb (L x); rewrite hML in hh.
have hn:=real_seminorm_nonnegative hNY.1 (L x).
rewrite div1r mulrC ler_pdivrMr //; nra.
Qed.

(** Source for [norm_linear_right_inverse_closed_range]: the
    differential of a diffeomorphism is onto, so its range is
    closed, as required in Federer 3.1.21, p. 234. *)
Lemma norm_linear_right_inverse_closed_range (R:realType) (X Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (L:Hom X Y) (M:Hom Y X) :
  cancel M L -> @closed (real_norm_metric_space hNY) (range L).
Proof.
move=>hLM.
have he:range L=setT.
  apply/seteqP; split=>y; first by [].
  move=>_; exists (M y); first exact I; exact (hLM y).
rewrite he; exact: closedT.
Qed.
