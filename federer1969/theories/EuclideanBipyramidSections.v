(** Federer (1969), 2.10.36, printed p. 198: the convex hull of the
    projected base and the two centred chord endpoints is contained in the
    Steiner image. Its horizontal sections contain homothetic copies of the
    base. The pure convexity statement below needs no measurability or
    compactness assumptions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanCoordinateSplit AffineDilation ProductSections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_join_affine_combination]: supporting
    Cartesian-coordinate identity for the convex-hull
    argument in 2.10.36, p. 198.
    It uses the proved linearity of
    the public head and tail inclusions. *)
Lemma euclidean_join_affine_combination (R : realType) (n : nat)
    (x y : inner_metric_space (@euclidean_inner_productP R n)*R) (w : R) :
  euclidean_join ((1-w)*:x.1+w*:y.1,(1-w)*x.2+w*y.2)=
    (1-w)*:euclidean_join x+w*:euclidean_join y.
Proof.
by rewrite /euclidean_join /= !linearD !linearZ addrACA.
Qed.

(** Source for [euclidean_join_base_apex_combination]: supporting
    section formula for the convex hull
    in 2.10.36, p. 198. At
    relative height w the base is
    contracted by 1-w towards the apex foot. *)
Lemma euclidean_join_base_apex_combination (R : realType) (n : nat)
    (x z : inner_metric_space (@euclidean_inner_productP R n)) (h w : R) :
  (1-w)*:euclidean_join (x,0)+w*:euclidean_join (z,h)=
    euclidean_join (affine_dilation z (1-w) x,w*h).
Proof.
rewrite -euclidean_join_affine_combination /= mulr0 add0r.
have he : 1-(1-w)=w by ring.
by rewrite /affine_dilation he addrC.
Qed.

(** Source for [convex_unit_bipyramid_section_inclusion]: supporting
    cross-section inclusion for the two-apex
    convex hull in 2.10.36, p. 198,
    after normalising its half-height to one.
    The base and ambient convex set
    may be arbitrary, including empty bases. *)
Theorem convex_unit_bipyramid_section_inclusion (R : realType) (n : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (C : set (inner_metric_space (@euclidean_inner_productP R n.+1)))
    (z : inner_metric_space (@euclidean_inner_productP R n)) :
  is_inner_convex C -> (forall x, K x -> C (euclidean_join (x,0))) ->
  C (euclidean_join (z,1)) -> C (euclidean_join (z,-1)) ->
  forall t : R, `|t|<=1 ->
    (affine_dilation z (1-`|t|)) @` K `<=`
      product_horizontal_section ((@euclidean_join R n) @^-1` C) t.
Proof.
move=> hC hbase hplus hminus t ht _ [x hx <-].
change (C (euclidean_join (affine_dilation z (1-`|t|) x,t))).
case: (leP 0 t)=> hsign.
- rewrite (ger0_norm hsign) in ht *.
  have hh := hC (euclidean_join (x,0)) (euclidean_join (z,1)) (hbase x hx) hplus t hsign ht.
  by rewrite euclidean_join_base_apex_combination mulr1 in hh.
- have hw : 0<= -t by rewrite oppr_ge0; exact: ltW hsign.
  rewrite (ltr0_norm hsign) in ht *.
  have hh := hC (euclidean_join (x,0)) (euclidean_join (z,-1)) (hbase x hx) hminus (-t) hw ht.
  have hprod : -t*(-1)=t by ring.
  by rewrite euclidean_join_base_apex_combination hprod in hh.
Qed.
