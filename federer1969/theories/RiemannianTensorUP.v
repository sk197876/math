(** Federer (1969), 3.2.46, printed pp. 280--281:
    a continuous field of positive inner products on an open Euclidean
    coordinate domain. The field is specified by its laws. No square-root
    frame, derivative field or global auxiliary linear map is selected. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerProductLaws InnerNorm NormDifferentialUP NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_continuous_riemannian_tensor]: the continuous map g
    taking inner-product values, Federer 3.2.46, p. 281, first paragraph.
    Continuity is expressed by homogeneous bilinear operator bounds,
    the norm topology on the finite-dimensional tensor space. The
    domain is open and no coordinate or auxiliary frame is selected. *)
Record is_continuous_riemannian_tensor (R : realType) n
    (A : R_n R n -> Prop) (g : R_n R n -> R_n R n -> R_n R n -> R) : Prop := {
  (** Source for [riemannian_tensor_inner]: g(x) is an inner product for
      each x in A, Federer 3.2.46, p. 281, first paragraph. *)
  riemannian_tensor_inner : forall x, A x -> is_inner_product (g x);
  (** Source for [riemannian_tensor_domain_open]: A is open,
      Federer 3.2.46, p. 281, first sentence. *)
  riemannian_tensor_domain_open : forall a, A a ->
    norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) A a;
  (** Source for [riemannian_tensor_continuous]: continuity of the
      bilinear tensor g in its operator norm, Federer 3.2.46, p. 281,
      expressed by homogeneous evaluation bounds rather than by an
      independently selected matrix norm. *)
  riemannian_tensor_continuous : forall a, A a -> forall e : R,
    0 < e -> exists d : R, 0 < d /\ forall h, A (a+h) ->
    inner_norm (@euclidean_inner_productP R n) h < d -> forall u v,
      `|g (a+h) u v - g a u v| <=
        e * inner_norm (@euclidean_inner_productP R n) u *
          inner_norm (@euclidean_inner_productP R n) v
}.

(** Source for [riemannian_tensor_speed]: the square-root speed
    (C'(t) tensor C'(t),g(C(t)))^(1/2) in Federer 3.2.46, p. 281,
    first defining integral. The scalar root is the existing root. *)
Definition riemannian_tensor_speed (R : realType) n
    (g : R_n R n -> R_n R n -> R_n R n -> R) x v :=
  Num.sqrt (g x v v).

(** Source for [riemannian_tensor_speed_nonnegative]: nonnegative
    curve speed in Federer 3.2.46, p. 281, first integral. This
    supporting assertion needs no positivity premise on g. *)
Lemma riemannian_tensor_speed_nonnegative (R : realType) n g x v :
  0 <= @riemannian_tensor_speed R n g x v.
Proof. exact: sqrtr_ge0. Qed.

(** Source for [riemannian_tensor_speed_inner_norm]: the actual inner
    norm is exactly the printed square root, Federer 3.2.46, p. 281.
    The inner-product proof is local to the original point x. *)
Lemma riemannian_tensor_speed_inner_norm (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x (hx : A x) v :
  riemannian_tensor_speed g x v = inner_norm (riemannian_tensor_inner hg hx) v.
Proof.
apply: esym; apply: inner_norm_value; first exact: sqrtr_ge0.
exact: sqr_sqrtr (inner_nonnegative (riemannian_tensor_inner hg hx) v).
Qed.

(** Source for [riemannian_tensor_pair_continuous]: ordinary pair
    evaluations of the continuous tensor are continuous, supporting
    Federer 3.2.46, p. 281. The operator-law definition therefore
    retains continuity of every actual coefficient. *)
Lemma riemannian_tensor_pair_continuous (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) u v :
  norm_class_zero (inner_norm (@euclidean_inner_productP R n))
    (fun t : R^o => `|t|) A (fun x => g x u v).
Proof.
move=> a ha; split; first exact: (@riemannian_tensor_domain_open R n A g hg a ha).
move=> e he.
pose M := inner_norm (@euclidean_inner_productP R n) u *
  inner_norm (@euclidean_inner_productP R n) v.
have hM : 0 <= M := mulr_ge0 (inner_norm_nonnegative _ _) (inner_norm_nonnegative _ _).
have hMp : 0 < M+1 by lra.
have hE : 0 < e/(M+1) by rewrite divr_gt0.
have [d [hd hControl]] := (@riemannian_tensor_continuous R n A g hg a ha (e/(M+1)) hE).
exists d; split=> // h hh hSmall.
have hB := hControl h hh hSmall u v.
have hScale : e/(M+1)*M < e.
  have hLt : e/(M+1)*M < e/(M+1)*(M+1).
    by rewrite (ltr_pM2l hE) ltrDl ltr01.
  have hMpne : M+1 != 0 := lt0r_neq0 hMp.
  have hCancel : e/(M+1)*(M+1) = e by rewrite (divfK hMpne).
  by rewrite hCancel in hLt.
apply: le_lt_trans hB _.
by rewrite -mulrA; exact hScale.
Qed.
