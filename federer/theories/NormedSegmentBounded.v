(** Federer (1969), 3.1.11, pp. 220–221:
    a continuous normed-vector curve is bounded on
    the compact parameter segment of the Taylor formula. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals topology normedtype lra.
From Federer Require Import RealNormUP RealMetricBackground MetricClosedBalls
  NormClassOneUP CompactFiniteCover NormedSegmentUniformContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_class_zero_real_segment_bounded]:
    boundedness on the compact path interval used
    to compare the ordinary and Stieltjes forms
    of Taylor's integral, Federer 3.1.11,
    pp. 220–221. The finite-cover proof
    does not assume the target is complete. *)
Theorem norm_class_zero_real_segment_bounded (R : realType)
    (Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (A : R->Prop) (f : R->Y) (a b : R) :
  (forall t, a<=t<=b -> A t) ->
  norm_class_zero (fun t : R^o=>`|t|) NY A f ->
  exists M : R, 0<M /\ forall t, a<=t<=b -> NY (f t)<=M.
Proof.
move=> hA hf.
have [d [hd hmod]] := norm_class_zero_real_segment_uniform hNY hA hf (@ltr01 R).
pose K : set (real_line_metric R) := [set t | a<=t<=b].
have hK : compact K.
  have hset : K=`[a,b].
    by apply/seteqP; split=> t; rewrite /K /= in_itv /=.
  rewrite hset; exact: segment_compact.
have hcover : K `<=` \bigcup_(c in K) [set y | mdist c y<d].
  move=> x hx; exists x=> //; change (is_true (mdist x x<d)); by rewrite mdistxx.
have [F hFK hF] := @compact_open_finite_cover (real_line_metric R)
  (real_line_metric R) K (fun c=>[set y | mdist c y<d]) K hK
  (fun c _=>metric_open_ball_open c d) hcover.
pose S := \sum_(i : F) NY (f (val i)).
have hS : 0<=S by apply: sumr_ge0=>i _; exact (real_seminorm_nonnegative hNY.1 (f (val i))).
have hterm (i : F) : NY (f (val i))<=S.
  rewrite /S (bigD1 i) //= lerDl.
  apply: sumr_ge0=>j _; exact (real_seminorm_nonnegative hNY.1 (f (val j))).
exists (S+1); split; first by lra.
move=> x hx; have [c hcf hcx] := hF x hx.
have hc : K c := set_mem (hFK c hcf).
have hsmall : NY (f x-f c)<1.
  rewrite (real_seminorm_subtract hNY.1); exact: hmod c x hc hx hcx.
have hid : f x=(f x-f c)+f c by rewrite subrK.
rewrite hid; apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
have hb := hterm ([` hcf]%fset).
change (is_true (NY (f c)<=S)) in hb; lra.
Qed.
