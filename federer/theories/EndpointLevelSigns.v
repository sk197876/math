(** Federer (1969), 3.2.6, p. 246: the net
    signed fibre count is one between ordered endpoint
    values and zero outside, with reversed orientation
    handled by a minus sign. Equal endpoint values give
    zero, as required by the erratum's weak inequality. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [oriented_level_indicator]: supporting signed
    indicator in the observation of Federer 3.2.6,
    p. 246. It is positive on a<y<b, negative
    on b<y<a, and zero elsewhere, including a=b. *)
Definition oriented_level_indicator (R:realType) (a b y:R):R:=
  (((a<y)&&(y<b))%R)%:R-(((b<y)&&(y<a))%R)%:R.

(** Source for [endpoint_level_sign_difference]: supporting
    endpoint calculation for the finite signed count in
    Federer 3.2.6, p. 246. Only the two endpoint
    levels are excluded; no strict ordering between endpoint
    values is assumed, retaining f(a)=f(b). *)
Lemma endpoint_level_sign_difference (R:realType) (a b y:R):
  a!=y -> b!=y ->
  Num.sg (b-y)-Num.sg (a-y)= 2*oriented_level_indicator a b y.
Proof.
move=>ha hb.
have hYa:(y<a)= ~~(a<y) by rewrite ltNge le_eqVlt (negbTE ha).
have hYb:(y<b)= ~~(b<y) by rewrite ltNge le_eqVlt (negbTE hb).
have hSignA:Num.sg (a-y)=(if a<y then -1 else 1).
  case:(ltP a y)=>hBelow.
  - by rewrite (ltr0_sg (_:a-y<0)) ?subr_lt0.
  - have hAbove:y<a by rewrite lt_neqAle eq_sym ha hBelow.
    by rewrite (gtr0_sg (_:0<a-y)) ?subr_gt0.
have hSignB:Num.sg (b-y)=(if b<y then -1 else 1).
  case:(ltP b y)=>hBelow.
  - by rewrite (ltr0_sg (_:b-y<0)) ?subr_lt0.
  - have hAbove:y<b by rewrite lt_neqAle eq_sym hb hBelow.
    by rewrite (gtr0_sg (_:0<b-y)) ?subr_gt0.
rewrite hSignA hSignB /oriented_level_indicator hYa hYb.
case:(a<y); case:(b<y)=>/=; lra.
Qed.
