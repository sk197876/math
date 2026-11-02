(** Positive coordinate changes supporting Federer (1969), 2.8.20, p. 152.
    Saks1934 Lemma B, p. 258, places a normalized finite group in each
    remaining rectangle; Cesari1939 Lemma III, p. 306, describes the same
    placement. These are elementary supporting coordinate identities, not a
    separate assertion of Federer. Only interval images are used; no
    change-of-variables theorem is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From mathcomp Require Import ring lra.
From Federer Require Import ScalarPlaneRectangles ScalarHalfOpenRectangles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Local Open Scope ring_scope.

(** Source for [rectangle_affine_map]: supporting placement map
    for Federer 2.8.20, p. 152; Saks1934 Lemma B,
    p. 258. Its positive factors will be hypotheses of the laws. *)
Definition rectangle_affine_map (R : realType) (a w c h : R) (p : R*R) :=
  (a+w * p.1,c+h * p.2)%R.

(** Source for [rectangle_affine_inverse]: supporting inverse
    for the positive placement map used for Federer 2.8.20,
    p. 152. Nonzero factors are required when proving cancellation. *)
Definition rectangle_affine_inverse (R : realType) (a w c h : R) (p : R*R) :=
  ((p.1-a)/w,(p.2-c)/h)%R.

(** Source for [rectangle_affine_cancel]: supporting cancellation
    for the placement in Saks1934 Lemma B, p. 258,
    used for Federer 2.8.20, p. 152. *)
Lemma rectangle_affine_cancel (R : realType) (a w c h : R) :
  (0<w)%R -> (0<h)%R ->
  cancel (rectangle_affine_map a w c h) (rectangle_affine_inverse a w c h).
Proof.
move=> hw hh [x y]; rewrite /rectangle_affine_map /rectangle_affine_inverse /=.
congr (_, _); by rewrite addrAC subrr add0r mulrAC mulfV ?gt_eqF // mul1r.
Qed.

(** Source for [rectangle_affine_inverse_cancel]: supporting
    reverse cancellation for the rectangle placement in Federer
    2.8.20, p. 152. *)
Lemma rectangle_affine_inverse_cancel (R : realType) (a w c h : R) :
  (0<w)%R -> (0<h)%R ->
  cancel (rectangle_affine_inverse a w c h) (rectangle_affine_map a w c h).
Proof.
move=> hw hh [x y]; rewrite /rectangle_affine_map /rectangle_affine_inverse /=.
congr (_, _); by rewrite mulrCA mulfV ?gt_eqF // mulr1 addrC subrK.
Qed.

(** Source for [positive_affine_interval_test]: supporting
    endpoint comparison for the finite group placements in
    Federer 2.8.20, p. 152. The flags allow open
    or closed endpoints without changing the underlying map. *)
Lemma positive_affine_interval_test (R : realType) (a w u v x : R)
    (l r : bool) : (0<w)%R ->
  (a+w*x \in Interval (BSide l (a+w*u)) (BSide r (a+w*v))) =
  (x \in Interval (BSide l u) (BSide r v)).
Proof.
by move=> hw; case: l; case: r; rewrite !in_itv /= ?lerD2l ?ltrD2l
  ?ler_pM2l // ?ltr_pM2l //.
Qed.

(** Source for [rectangle_affine_closed_image]: supporting
    closed rectangle placement for Federer 2.8.20, p. 152.
    The image is a compact rectangle with the transformed endpoints. *)
Lemma rectangle_affine_closed_image (R : realType) (a w c h u v s t : R) :
  (0<w)%R -> (0<h)%R ->
  rectangle_affine_map a w c h @` scalar_closed_rectangle u v s t =
  scalar_closed_rectangle (a+w*u) (a+w*v) (c+h*s) (c+h*t).
Proof.
move=> hw hh; apply/seteqP; split.
- move=> p [[x y] hx <-]; move: hx.
  by rewrite /scalar_closed_rectangle /rectangle_affine_map /= !positive_affine_interval_test.
- move=> p hp; exists (rectangle_affine_inverse a w c h p).
  + have hp' := hp.
    rewrite -(rectangle_affine_inverse_cancel a c hw hh p) in hp'.
    move: hp'.
    by rewrite /scalar_closed_rectangle /rectangle_affine_map /= !positive_affine_interval_test.
  + exact (@rectangle_affine_inverse_cancel R a w c h hw hh p).
Qed.

(** Source for [rectangle_affine_half_open_image]: supporting
    half-open auxiliary rectangle placement for Federer 2.8.20,
    p. 152. Eligible rectangles remain closed. *)
Lemma rectangle_affine_half_open_image (R : realType) (a w c h u v s t : R) :
  (0<w)%R -> (0<h)%R ->
  rectangle_affine_map a w c h @` scalar_half_open_rectangle u v s t =
  scalar_half_open_rectangle (a+w*u) (a+w*v) (c+h*s) (c+h*t).
Proof.
move=> hw hh; apply/seteqP; split.
- move=> p [[x y] hx <-]; move: hx.
  by rewrite /scalar_half_open_rectangle /rectangle_affine_map /= !positive_affine_interval_test.
- move=> p hp; exists (rectangle_affine_inverse a w c h p).
  + have hp' := hp.
    rewrite -(rectangle_affine_inverse_cancel a c hw hh p) in hp'.
    move: hp'.
    by rewrite /scalar_half_open_rectangle /rectangle_affine_map /= !positive_affine_interval_test.
  + exact (@rectangle_affine_inverse_cancel R a w c h hw hh p).
Qed.

(** Source for [rectangle_affine_strip_image]: supporting
    image of the disjoint vertical strips used for the
    harmonic area gain in Federer 2.8.20, p. 152. *)
Lemma rectangle_affine_strip_image (R : realType) (a w c h u v s t : R) :
  (0<w)%R -> (0<h)%R ->
  rectangle_affine_map a w c h @` scalar_half_open_strip u v s t =
  scalar_half_open_strip (a+w*u) (a+w*v) (c+h*s) (c+h*t).
Proof.
move=> hw hh; apply/seteqP; split.
- move=> p [[x y] hx <-]; move: hx.
  by rewrite /scalar_half_open_strip /rectangle_affine_map /= !positive_affine_interval_test.
- move=> p hp; exists (rectangle_affine_inverse a w c h p).
  + have hp' := hp.
    rewrite -(rectangle_affine_inverse_cancel a c hw hh p) in hp'.
    move: hp'.
    by rewrite /scalar_half_open_strip /rectangle_affine_map /= !positive_affine_interval_test.
  + exact (@rectangle_affine_inverse_cancel R a w c h hw hh p).
Qed.

(** Source for [rectangle_affine_closed_area]: supporting
    area scaling of an individual rectangle in the finite
    placement for Federer 2.8.20, p. 152. This
    follows from side lengths, rather than an assumed transformation
    formula for arbitrary measurable sets. *)
Lemma rectangle_affine_closed_area (R : realType) (a w c h u v s t : R) :
  (0<w)%R -> (0<h)%R -> (u<=v)%R -> (s<=t)%R ->
  scalar_plane_lebesgue (rectangle_affine_map a w c h @` scalar_closed_rectangle u v s t) =
  ((w*h)%:E * scalar_plane_lebesgue (scalar_closed_rectangle u v s t))%E.
Proof.
move=> hw hh huv hst; rewrite rectangle_affine_closed_image //
  !scalar_closed_rectangle_value // ?lerD2l ?ler_pM2l // -EFinM.
congr (_%:E); ring.
Qed.

(** Source for [rectangle_affine_strip_area]: supporting
    area scaling of each disjoint strip for the harmonic
    gain in Federer 2.8.20, p. 152. *)
Lemma rectangle_affine_strip_area (R : realType) (a w c h u v s t : R) :
  (0<w)%R -> (0<h)%R -> (u<=v)%R -> (s<=t)%R ->
  scalar_plane_lebesgue (rectangle_affine_map a w c h @` scalar_half_open_strip u v s t) =
  ((w*h)%:E * scalar_plane_lebesgue (scalar_half_open_strip u v s t))%E.
Proof.
move=> hw hh huv hst; rewrite rectangle_affine_strip_image //
  !scalar_half_open_strip_value // ?lerD2l ?ler_pM2l // -EFinM.
congr (_%:E); ring.
Qed.
