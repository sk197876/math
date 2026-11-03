(** Federer (1969), 3.2.41, printed p. 277, first proof paragraph:
    each coordinate sum P_j+Q_j is the open interval with summed
    endpoints. This supporting scalar statement proves the actual
    pair decomposition, including every interior point. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_open_interval_sum]: supporting exact interval
    addition in Federer 3.2.41, p. 277. Two proper bounded open
    intervals sum to the proper open interval of endpoint sums.
    The intermediate scalar choices remain existential. *)
Theorem scalar_open_interval_sum (R : realType) (a b c d z : R) :
  a<b -> c<d ->
  (a+c<z<b+d <-> exists x y, a<x<b /\ c<y<d /\ z=x+y).
Proof.
move=> hab hcd; split.
- move=> /andP[hz0 hz1].
  pose D : R := (b-a)+(d-c).
  have hD : 0<D by rewrite /D; lra.
  have hD0 : D!=0 by rewrite gt_eqF.
  pose t : R := (z-(a+c))/D.
  have ht0 : 0<t by rewrite /t divr_gt0 // subr_gt0.
  have ht1 : t<1.
    rewrite /t ltr_pdivrMr // mul1r /D; lra.
  have hCancel : t*D=z-(a+c) by rewrite /t divfK.
  rewrite /D mulrDr in hCancel.
  exists (a+t*(b-a)),(c+t*(d-c)).
  split; first by apply/andP; split; nra.
  split; first by apply/andP; split; nra.
  lra.
- move=> [x [y [/andP[hax hxb] [/andP[hcy hyd] ->]]]].
  apply/andP; split; lra.
Qed.
