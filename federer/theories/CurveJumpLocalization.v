(** Supporting the endpoint ranges of the jump sums in Federer (1969),
    2.10.14, p. 177. Retract the source onto [a,b] as in 2.5.18(2), p. 112.
    Right jumps are retained on [a,b) and left jumps on (a,b]; all other
    one-sided jumps of the retracted curve vanish. No variation hypothesis
    is needed for these local upper-limit identities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import CurveOneSidedJumpUP CurveOneSidedJumpContinuity StieltjesSubstitution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [segment_retraction_below]: supporting constant left
    tail of the interval-local representative in 2.10.14, p. 177,
    from the retraction of 2.5.18(2), p. 112. *)
Lemma segment_retraction_below (R : realType) (a b t : R) :
  (a<=b)%R -> (t<=a)%R -> segment_retraction a b t=a.
Proof.
move=> hab hta; rewrite /segment_retraction min_l ?(le_trans hta hab) //.
by rewrite max_l.
Qed.

(** Source for [segment_retraction_above]: supporting constant right
    tail of the interval-local representative in 2.10.14, p. 177,
    using 2.5.18(2), p. 112. *)
Lemma segment_retraction_above (R : realType) (a b t : R) :
  (a<=b)%R -> (b<=t)%R -> segment_retraction a b t=b.
Proof. by move=> hab hbt; rewrite /segment_retraction min_r // max_r. Qed.

(** Source for [constant_curve_one_sided_jump_zero]: supporting
    zero-jump tail in 2.10.14, p. 177. Constant curves
    have zero distance upper limit from either side. *)
Lemma constant_curve_one_sided_jump_zero (R : realType) (Y : metricType R)
    (c : Y) (right : bool) (x : R) : curve_one_sided_jump (fun _ : R => c) right x=0.
Proof. apply: curve_continuous_one_sided_jump_zero; exact: cvg_cst. Qed.

(** Source for [curve_right_jump_retracted]: supporting exact
    [a,b) range of alpha_+ in 2.10.14, p. 177.
    Retraction retains the right jump at a and removes the
    right jump at b; it adds no tail jumps. *)
Theorem curve_right_jump_retracted (R : realType) (Y : metricType R)
    (g : R -> Y) (a b x : R) : (a<=b)%R ->
  curve_right_jump_size (g \o @segment_retraction R a b) x=
    if (a<=x<b)%R then curve_right_jump_size g x else 0.
Proof.
move=> hab.
pose h := g \o @segment_retraction R a b.
change (curve_one_sided_jump h true x=if (a<=x<b)%R then curve_right_jump_size g x else 0).
case: ifP=> hdom.
- have /andP[hax hxb] := hdom.
  apply: (@curve_one_sided_jump_local_equal R Y h g true x (b-x)%R).
  + by rewrite subr_gt0.
  + move=> t; rewrite /curve_side_offset /= => /andP[hxt htb].
    have ht : (a<=t<=b)%R by apply/andP; split; lra.
    by rewrite /h /= segment_retraction_id.
- case: (leP a x)=> hax.
  + have hbx : (b<=x)%R.
      rewrite leNgt; apply/negP=> hxb; by move: hdom; rewrite hax hxb.
    have he : curve_one_sided_jump h true x=curve_one_sided_jump (fun _ => g b) true x.
      apply: (@curve_one_sided_jump_local_equal R Y h (fun _ => g b) true x 1%R ltr01).
      move=> t; rewrite /curve_side_offset /= => /andP[hxt _].
      have hbt : (b<=t)%R by lra.
      by rewrite /h /= (segment_retraction_above hab hbt).
    by rewrite he constant_curve_one_sided_jump_zero.
  + have hd : (0<a-x)%R by rewrite subr_gt0.
    have he : curve_one_sided_jump h true x=curve_one_sided_jump (fun _ => g a) true x.
      apply: (@curve_one_sided_jump_local_equal R Y h (fun _ => g a) true x (a-x)%R hd).
      move=> t; rewrite /curve_side_offset /= => /andP[_ hta].
      have hta' : (t<=a)%R by lra.
      by rewrite /h /= (segment_retraction_below hab hta').
    by rewrite he constant_curve_one_sided_jump_zero.
Qed.

(** Source for [curve_left_jump_retracted]: supporting exact
    (a,b] range of alpha_- in 2.10.14, p. 177.
    Retraction removes the left jump at a and retains the
    left jump at b, without assumptions outside [a,b]. *)
Theorem curve_left_jump_retracted (R : realType) (Y : metricType R)
    (g : R -> Y) (a b x : R) : (a<=b)%R ->
  curve_left_jump_size (g \o @segment_retraction R a b) x=
    if (a<x<=b)%R then curve_left_jump_size g x else 0.
Proof.
move=> hab.
pose h := g \o @segment_retraction R a b.
change (curve_one_sided_jump h false x=if (a<x<=b)%R then curve_left_jump_size g x else 0).
case: ifP=> hdom.
- have /andP[hax hxb] := hdom.
  apply: (@curve_one_sided_jump_local_equal R Y h g false x (x-a)%R).
  + by rewrite subr_gt0.
  + move=> t; rewrite /curve_side_offset /= => /andP[htx hat].
    have ht : (a<=t<=b)%R by apply/andP; split; lra.
    by rewrite /h /= segment_retraction_id.
- case: (leP x b)=> hxb.
  + have hxa : (x<=a)%R.
      rewrite leNgt; apply/negP=> hax; by move: hdom; rewrite hax hxb.
    have he : curve_one_sided_jump h false x=curve_one_sided_jump (fun _ => g a) false x.
      apply: (@curve_one_sided_jump_local_equal R Y h (fun _ => g a) false x 1%R ltr01).
      move=> t; rewrite /curve_side_offset /= => /andP[htx _].
      have hta : (t<=a)%R by lra.
      by rewrite /h /= (segment_retraction_below hab hta).
    by rewrite he constant_curve_one_sided_jump_zero.
  + have hd : (0<x-b)%R by rewrite subr_gt0.
    have he : curve_one_sided_jump h false x=curve_one_sided_jump (fun _ => g b) false x.
      apply: (@curve_one_sided_jump_local_equal R Y h (fun _ => g b) false x (x-b)%R hd).
      move=> t; rewrite /curve_side_offset /= => /andP[_ hbt].
      have hbt' : (b<=t)%R by lra.
      by rewrite /h /= (segment_retraction_above hab hbt').
    by rewrite he constant_curve_one_sided_jump_zero.
Qed.
