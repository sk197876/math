(** Federer (1969), 3.1.24, p. 240: the set
    where every differential vanishes is open. The key local
    statement follows from the uniform Taylor expansion. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormDifferentialUP NormClassOneUP NormRegularity NormHigherDifferentialUP NormHigherDifferentialLocal
  NormAnalyticUP NormAnalyticDiagonal NormAnalyticTaylor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_analytic_flat_locally_zero]: supporting
    the openness of W in Federer 3.1.24, p. 240.
    If every actual differential at an analytic point is zero,
    all Taylor sums vanish, and uniform convergence forces the
    function to vanish throughout an open neighbourhood. This
    implication needs no completeness or finite-dimensionality. *)
Theorem norm_analytic_flat_locally_zero (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (f:X->Y) a :
  @norm_analytic_at R X Y NX NY hNX hNY A f a ->
  (forall m (z:@ContinuousMultilinear.space R m X Y NX NY hNX hNY),
    has_norm_higher_differential NX
      (fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY)
      (fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY) A f m a z -> z=0) ->
  exists U:X->Prop,U a /\ (forall x,U x -> A x) /\
    (forall x,U x -> norm_domain_interior NX U x) /\ forall x,U x -> f x=0.
Proof.
move=>hf hflat.
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ev i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose ZN i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ i:=@ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
have ht:=@norm_diagonal_analytic_taylor R X Y NX NY hNX hNY A f a
  (@norm_analytic_diagonal R X Y NX NY hNX hNY A f a hf).
move:ht=>[U [ha [hUA [hc [D [hD hlim]]]]]].
have hOpen x (hx:U x):norm_domain_interior NX U x:=((hc 0%N).1 x hx).1.
have hDz m:D m= 0.
  apply: hflat.
  exact ((@norm_higher_differential_open_restriction R X Y NX NY hNX hNY Z ev ZN hZ
    m A U f hUA hOpen a ha (D m)).2 (hD m)).
have hsum n x:(\sum_(m<n.+1) (m`!)%:R^-1 *: ev m [ffun i=>x-a] (D m))= 0.
  apply: big1=>m _; by rewrite hDz linear0 scaler0.
exists U; split; first exact ha.
split; first exact hUA.
split; first exact hOpen.
move=>x hx; apply: hNY.2.
apply/eqP; rewrite eq_le; apply/andP; split; last exact (real_seminorm_nonnegative hNY.1 _).
rewrite leNgt; apply/negP=>hpos.
have he:0<NY (f x)/2 by rewrite divr_gt0 // ltr0n.
have [n hn]:=hlim (NY (f x)/2) he.
have hh:=hn n (leqnn n) x hx.
rewrite hsum subr0 in hh; lra.
Qed.
