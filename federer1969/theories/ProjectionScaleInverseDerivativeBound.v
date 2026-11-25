(** Federer (1969), 3.2.31, p. 269: supporting the
    inverse-rescaled derivative estimate. Only the abstract
    range-idempotent, scaling and operator-norm laws are used. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  OperatorNormUP SymmetricRangeIdempotentUP ProjectionScaleAutomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [projection_scale_inverse_derivative_bound]:
    supporting the strict inverse-derivative bound in Federer
    3.2.31, p. 269. On the actual range of D, the inverse
    automorphism scales by M^-1. Its abstract operator-norm
    laws and the proved scalar ratio c/M<=1/2 imply the actual
    pointwise half-contraction, without exposing a projection
    or automorphism implementation. *)
Lemma projection_scale_inverse_derivative_bound (R:realType) m v
    (D:Hom (R_n R m) (R_n R v)) (P:Hom (R_n R v) (R_n R v))
    (M d:R) (T U:Hom (R_n R v) (R_n R v)) c:
  @is_symmetric_range_idempotent R (R_n R m) (R_n R v) (@euclidean_inner_product R v) D P ->
  @is_projection_scale_automorphism R (R_n R v) (@euclidean_inner_product R v) P M d T U ->
  is_operator_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R v) (hom_as_linear D) c ->
  0<M ->c/M<=1/2 ->forall x,
    inner_norm (@euclidean_inner_productP R v) (U (D x))<=
      (1/2)*inner_norm (@euclidean_inner_productP R m) x.
Proof.
move=>hP hT hNorm hM hRatio x.
have hPD:P (D x)=D x.
  apply:(@range_idempotent_fixed_range R (R_n R m) (R_n R v)
    (@euclidean_inner_product R v) D P hP (D x)).2.
  by exists x.
have hU:=@projection_scale_inverse_range R (R_n R v) (@euclidean_inner_product R v)
  P M d T U hT (D x).
rewrite hPD in hU.
have hInv:0<=M^-1 by rewrite invr_ge0; exact:ltW hM.
rewrite hU inner_normZ (ger0_norm hInv).
have hPoint:=operator_norm_vector_bound hNorm x.
change (is_true (inner_norm (@euclidean_inner_productP R v) (D x)<=
  c*inner_norm (@euclidean_inner_productP R m) x)) in hPoint.
apply:(le_trans (ler_wpM2l hInv hPoint)).
rewrite mulrA (mulrC M^-1 c).
exact (ler_wpM2r (inner_norm_nonnegative (@euclidean_inner_productP R m) x) hRatio).
Qed.
