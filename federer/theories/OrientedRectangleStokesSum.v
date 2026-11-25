(** Federer (1969), 4.1.8, p. 362: the
    original finite sum of endpoint faces, with
    the printed one-based sign (-1)^k. These
    algebraic sum identities use the original face
    recurrence and binary product bilinearity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear OrientedSegmentFactor OrientedRectangleDomain OrientedRectangleSpaces
  OrientedRectangleCurrentSealed OrientedRectangleFacesUP OrientedRectangleFacesSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section OrientedRectangleStokesSum.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation Factor := (oriented_segment_factor R).
Local Notation Face := (fun f=>@oriented_rectangle_space R h2 f (size f).-1).
Local Notation Product := (@oriented_rectangle_product R h2).
Local Notation P := (@OrientedRectangleCurrent.value R h2).
Local Notation F := (fun f k=>@OrientedRectangleFaces.value R h2 f k).
Local Notation S := (@oriented_segment_factor_current R h2).
Local Notation Delta := (@oriented_segment_factor_endpoint_difference R h2).

(** Source for [oriented_rectangle_stokes_sum]: the exact
    original sum from k=1 to nu with coefficient
    (-1)^k and endpoint difference delta_(u_k)-delta_(v_k),
    Federer 4.1.8, p. 362. Our ordinal k has
    printed index k+1. *)
Definition oriented_rectangle_stokes_sum (f:seq Factor):Face f:=
  \sum_(k < size f) (-1:R)^+(val k).+1*:F f k.

(** Source for [oriented_rectangle_stokes_sum_single]: the
    original one-factor sum is delta_v-delta_u,
    supporting Federer 4.1.8, p. 362. *)
Lemma oriented_rectangle_stokes_sum_single a:
  oriented_rectangle_stokes_sum [::a]= -Delta a.
Proof.
rewrite /oriented_rectangle_stokes_sum big_ord1
  ((@OrientedRectangleFaces.laws R h2).1 a ord0) expr1 scaleN1r;by [].
Qed.

(** Source for [oriented_rectangle_stokes_sum_cons]: separating
    the first face gives its negative endpoint
    difference product minus the first segment times
    the remaining face sum, supporting the printed
    induction in Federer 4.1.8, p. 362. *)
Lemma oriented_rectangle_stokes_sum_cons a b t:
  oriented_rectangle_stokes_sum (a::b::t)=
    -Product a b t 0%N (size (b::t)) (Delta a) (P (b::t))-
    Product a b t 1%N (size (b::t)).-1 (S a) (oriented_rectangle_stokes_sum (b::t)).
Proof.
pose L:Hom (Face (b::t)) (Face (a::b::t)):=
  @HomMap R (Face (b::t)) (Face (a::b::t))
    (Product a b t 1%N (size (b::t)).-1 (S a))
    (introT (asboolP _) ((@oriented_rectangle_product_bilinear R h2 a b t 1%N (size (b::t)).-1).2 (S a))).
have hLinear:L (oriented_rectangle_stokes_sum (b::t))=
    \sum_(k < size (b::t)) (-1:R)^+(val k).+1*:
      Product a b t 1%N (size (b::t)).-1 (S a) (F (b::t) k).
  rewrite /oriented_rectangle_stokes_sum linear_sum.
  apply:eq_bigr=>k _;exact:linearZ.
have hTail:(\sum_(k < size (b::t)) (-1:R)^+(val (lift ord0 k)).+1*:
      F (a::b::t) (lift ord0 k))=
    -L (oriented_rectangle_stokes_sum (b::t)).
  rewrite hLinear -sumrN;apply:eq_bigr=>k _.
  have hIndex:val (lift ord0 k)=(val k).+1:=@lift0 (size (b::t)) k.
  rewrite ((@OrientedRectangleFaces.laws R h2).2.2 a b t k) hIndex exprS.
  by rewrite mulN1r scaleNr.
rewrite /oriented_rectangle_stokes_sum big_ord_recl.
rewrite ((@OrientedRectangleFaces.laws R h2).2.1 a b t) expr1 scaleN1r hTail.
by [].
Qed.
End OrientedRectangleStokesSum.
