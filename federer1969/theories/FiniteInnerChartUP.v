(** Federer (1969), 3.2.28, printed pp. 263–267: the finite
    inner-product spaces Hom, exterior powers and symmetric powers
    are suitable Euclidean ambient spaces. Their coordinate charts
    are specified by linear inverse and inner-product laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_finite_inner_chart]: isometric Euclidean
    coordinates on the finite inner-product ambient spaces of
    Federer 3.2.28, pp. 263–267; the underlying orthonormal
    basis identification is 1.7.1, p. 28. Both inverse laws
    and the metric normalization are obligations, not axioms. *)
Record is_finite_inner_chart (R:realType) (V:lmodType R)
    (B:V->V->R) n (e:Hom (R_n R n) V) (p:Hom V (R_n R n)):Prop:={
  (** Source for [finite_inner_chart_left_inverse]: the
      orthonormal coordinate inverse, 1.7.1, p. 28, used for
      the ambient identifications of 3.2.28, pp. 263–267. *)
  finite_inner_chart_left_inverse:cancel e p;
  (** Source for [finite_inner_chart_right_inverse]: all vectors
      have orthonormal coordinates, 1.7.1, p. 28, used in
      3.2.28, pp. 263–267. *)
  finite_inner_chart_right_inverse:cancel p e;
  (** Source for [finite_inner_chart_product]: the identification
      is isometric for the stated inner product, 1.7.1, p. 28,
      used for the Hausdorff volumes in 3.2.28, pp. 263–267. *)
  finite_inner_chart_product:forall x y,
    B (e x) (e y)= euclidean_inner_product x y
}.

(** Source for [finite_inner_chart_inverse_product]: preservation
    of the inner product in the inverse coordinates, supporting
    Federer 3.2.28, pp. 263–267. *)
Lemma finite_inner_chart_inverse_product (R:realType) (V:lmodType R)
    (B:V->V->R) n (e:Hom (R_n R n) V) (p:Hom V (R_n R n)):
  is_finite_inner_chart B e p ->forall x y,
    euclidean_inner_product (p x) (p y)= B x y.
Proof.
move=>h x y; rewrite -(finite_inner_chart_product h)
  !(finite_inner_chart_right_inverse h); reflexivity.
Qed.

(** Source for [finite_inner_chart_norm]: preservation of the
    stated Euclidean norm, supporting the Hausdorff identifications
    in Federer 3.2.28, pp. 263–267. *)
Lemma finite_inner_chart_norm (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n)):
  is_finite_inner_chart B e p ->forall x,
    inner_norm hB (e x)= inner_norm (@euclidean_inner_productP R n) x.
Proof.
move=>h x; apply:inner_norm_value; first exact:inner_norm_nonnegative.
by rewrite inner_norm_sqr (finite_inner_chart_product h).
Qed.

(** Source for [finite_inner_chart_inverse_norm]: preservation of
    norm by inverse coordinates, supporting Federer 3.2.28,
    pp. 263–267. *)
Lemma finite_inner_chart_inverse_norm (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n)):
  is_finite_inner_chart B e p ->forall x,
    inner_norm (@euclidean_inner_productP R n) (p x)= inner_norm hB x.
Proof.
move=>h x; rewrite -(finite_inner_chart_norm hB h (p x))
  (finite_inner_chart_right_inverse h); reflexivity.
Qed.
