(** Supporting homotheties for the closed convex comparison in Federer
    (1969), 2.10.4(2), p. 172. Work with the affine formula (1-t)a+t x. Its
    composition and inverse laws, together with the proved open convex
    contraction lemma, put the closure inside each strict enlargement. This
    supplies a proof ingredient without assuming a convex-boundary volume
    theorem. Source context: OpenConvexContractions.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import InnerProductUP InnerMetric InnerConvex OpenConvexContractions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [affine_dilation]: supporting homothetic
    enlargement used for Federer 2.10.4(2), p. 172.
    This is a named proof map, not a new object
    claimed to be defined separately in the book. *)
Definition affine_dilation (R : realFieldType) (V : lmodType R)
    (a : V) (t : R) (x : V) := (1-t)*:a+t*:x.

(** Source for [affine_dilation_compose]: supporting
    composition of the homotheties used in the
    generator comparison of Federer 2.10.4(2), p. 172. *)
Lemma affine_dilation_compose (R : realFieldType) (V : lmodType R)
    (a : V) (s t : R) (x : V) :
  affine_dilation a s (affine_dilation a t x)=affine_dilation a (s*t) x.
Proof.
rewrite /affine_dilation scalerDr !scalerA addrA -scalerDl.
by rewrite mulrBr mulr1 addrA subrK.
Qed.

(** Source for [affine_dilation_one]: supporting identity
    parameter for the homotheties in the proof of
    Federer 2.10.4(2), p. 172. *)
Lemma affine_dilation_one (R : realFieldType) (V : lmodType R)
    (a x : V) : affine_dilation a 1 x=x.
Proof. by rewrite /affine_dilation subrr scale0r scale1r add0r. Qed.

(** Source for [affine_dilation_inverse]: supporting inverse
    law for strict enlargements in the proof of
    Federer 2.10.4(2), p. 172. *)
Lemma affine_dilation_inverse (R : realFieldType) (V : lmodType R)
    (a x : V) (t : R) : t!=0 -> affine_dilation a t (affine_dilation a t^-1 x)=x.
Proof. by move=> ht; rewrite affine_dilation_compose mulfV // affine_dilation_one. Qed.

(** Source for [open_convex_closure_dilation_cover]: supporting
    closure replacement in Federer 2.10.4(2), p. 172.
    Strictly dilate an open convex set about one of
    its points to contain its closure. No boundedness
    or finite-dimensionality assumption is required. *)
Theorem open_convex_closure_dilation_cover (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (U : set (inner_metric_space hB)) (a : inner_metric_space hB) (t : R) :
  open U -> @is_inner_convex R V U -> U a -> 1<t ->
  closure U `<=` (@affine_dilation R V a t) @` U.
Proof.
move=> ho hc ha ht x hx.
have ht0 : 0<t := lt_trans ltr01 ht.
have hs0 : 0<t^-1 by rewrite invr_gt0.
have hs1 : t^-1<1 by rewrite invf_lt1.
have htN : t!=0 by rewrite (gt_eqF ht0).
exists (@affine_dilation R V a t^-1 x).
- exact (@open_convex_contraction_closure R V B hB U a x t^-1 ho hc ha hx hs0 hs1).
- exact (@affine_dilation_inverse R V a x t htN).
Qed.
