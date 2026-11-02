(** Federer (1969), 3.1.1, p. 211: the remainder inequalities
    define relatively closed tests on the open domain times Z.
    The proof below gives openness of each strict violation.
    Values of the total representative outside its actual domain
    are never used; both a and a+h must belong to that domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormOperatorNormUP
  ContinuousOperatorUP ContinuousOperatorNorm ContinuousOperatorEvaluation
  NormClassOneUP NormClassZeroTopology NormRemainderVariation MetricProductBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_differential_remainder_violation_open]:
    supporting open complement of a fixed-increment closed test
    in 3.1.1, p. 211. The increment and threshold are arbitrary;
    no separability or completeness hypothesis is needed here. *)
Theorem norm_differential_remainder_violation_open (R : realType)
    (X Y Z : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (evaluation : Hom Z (Hom X Y)) (ZN : Z -> R)
    (hZ : is_continuous_operator_space NX NY evaluation ZN)
    (A : set X) (f : X -> Y) (h : X) (c : R) :
  norm_class_zero NX NY A f ->
  open [set p : metric_product (real_norm_metric_space hNX)
      (real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ)) |
    A p.1 /\ A (p.1+h) /\ c<NY (f (p.1+h)-f p.1-evaluation p.2 h)].
Proof.
move=> hf; rewrite openE=> p [ha [hah hc]].
pose E := real_norm_metric_space hNX.
pose T := real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ).
pose eps := (NY (f (p.1+h)-f p.1-evaluation p.2 h)-c)/4.
have heps : 0<eps by rewrite /eps divr_gt0 // subr_gt0.
have [r [hr hnear]] := norm_class_zero_local_control hNX hf ha heps.
have [s [hs hnearh]] := norm_class_zero_local_control hNX hf hah heps.
have hNh := real_seminorm_nonnegative hNX.1 h.
have hden : 0<NX h+1 by lra.
pose d := eps/(NX h+1).
have hd : 0<d by rewrite /d divr_gt0.
apply: (proj2 (metricType_numDomainType.nbhs_mdistP p _)).
exists (Num.min r (Num.min s d)); first by rewrite /= !lt_min hr hs hd.
move=> q hq.
change (is_true (Num.max (NX (p.1-q.1)) (ZN (p.2-q.2))<Num.min r (Num.min s d))) in hq.
move: hq; rewrite gt_max !lt_min=> /andP [/andP [hxr /andP [hxs hxd]] /andP [hzr /andP [hzs hzd]]].
have hqr : NX (q.1-p.1)<r by rewrite (real_seminorm_subtract hNX.1).
have hqs : NX ((q.1+h)-(p.1+h))<s.
  by rewrite (addrC p.1 h) opprD addrA addrK (real_seminorm_subtract hNX.1).
have [hqa hfa] := hnear q.1 hqr.
have [hqah hfah] := hnearh (q.1+h) hqs.
split=> //; split=> //.
have hbound := @continuous_operator_evaluation_distance R X Y Z NX NY hNY evaluation ZN hZ h p.2 q.2.
change (is_true (NY (evaluation p.2 h-evaluation q.2 h)<=NX h*ZN (p.2-q.2))) in hbound.
have hev : NY (evaluation p.2 h-evaluation q.2 h)<eps.
  apply: le_lt_trans hbound _.
  have hz0 := norm_operator_nonnegative (continuous_operator_norm_laws hZ (p.2-q.2)).
  have hle : NX h*ZN (p.2-q.2)<=(NX h+1)*ZN (p.2-q.2) by nra.
  apply: le_lt_trans hle _.
  rewrite mulrC -ltr_pdivlMr //; exact hzd.
have hv := norm_remainder_variation_bound hNY
  (f (p.1+h)) (f p.1) (evaluation p.2 h)
  (f (q.1+h)) (f q.1) (evaluation q.2 h).
rewrite (real_seminorm_subtract hNY.1 (f (p.1+h)) (f (q.1+h)))
  (real_seminorm_subtract hNY.1 (f p.1) (f q.1)) in hv.
rewrite /eps in heps hfa hfah hev; lra.
Qed.
