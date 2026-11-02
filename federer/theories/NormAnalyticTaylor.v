(** Federer (1969), 3.1.24, p. 238: diagonal
    analytic bounds imply a uniformly convergent Taylor expansion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormRegularity NormRegularityOperations NormHigherDifferentialUP NormHigherDifferentialLocal
  NormClassOneUP NormOpenDomainLaws NormAnalyticUP NormAnalyticNonnegative NormSmoothFields
  NormDiagonalHomogeneousBound NormTaylorDiagonalBound NormTaylorRemainderBound GeometricUniformTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_diagonal_analytic_taylor]: the implication
    (2) to (3) of Federer 3.1.24, p. 238.
    Shrink to a norm ball with (c+1)r<1 and use
    the Taylor integral to bound the remainder after degree m
    by 2[(c+1)r]^m. This slightly weaker geometric estimate
    than the printed next-degree bound has the same uniform
    convergence consequence and retains zero values of c. *)
Theorem norm_diagonal_analytic_taylor (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) a :
  @norm_diagonal_analytic_at R X Y NX NY hNX hNY A f a ->
  @norm_taylor_analytic_at R X Y NX NY hNX hNY A f a.
Proof.
move=>[U [c [ha [hUA [hf hb]]]]].
pose Z:=fun m=>@ContinuousMultilinear.space R m X Y NX NY hNX hNY.
pose ev:=fun m=>@ContinuousMultilinear.evaluation R m X Y NX NY hNX hNY.
pose ZN:=fun m=>@ContinuousMultilinear.norm R m X Y NX NY hNX hNY.
pose hZ:=fun m=>@ContinuousMultilinear.laws R m X Y NX NY hNX hNY.
have hc:0<=c:=norm_diagonal_witness_nonnegative ha hf hb.
have hcp:0<c+1 by lra.
have [r0 [hr0 hBall]]:=(@norm_class_continuous R X Y NX NY hNX hNY U f 0 (hf 0%N) a ha).1.
pose r:=Num.min r0 (c+1)^-1/2.
have hmin:0<Num.min r0 (c+1)^-1 by rewrite lt_min hr0 invr_gt0.
have hr:0<r by rewrite /r divr_gt0 // ltr0n.
have hrmin:r<Num.min r0 (c+1)^-1 by rewrite /r; lra.
have hrr0:r<r0.
  apply: lt_le_trans hrmin _; by rewrite ge_min lexx.
have hrinv:r<(c+1)^-1.
  apply: lt_le_trans hrmin _; by rewrite ge_min lexx orbT.
pose q:=(c+1)*r.
have hq:0<q<1.
  apply/andP; split; first exact (mulr_gt0 hcp hr).
  move: hrinv; by rewrite -div1r ltr_pdivlMr // mulrC.
pose W:=fun x=>NX (x-a)<r.
have hWa:W a by rewrite /W subrr (real_seminorm_zero hNX.1).
have hWU x (hx:W x):U x.
  have hh:=hBall (x-a) (lt_trans hx hrr0); by rewrite addrC subrK in hh.
have hWopen x (hx:W x):norm_domain_interior NX W x.
  exact (@norm_open_ball_domain_interior R X NX hNX a r x hx).
have hfW:norm_class_all_orders hNX hNY W f.
  move=>m; exact (@norm_class_open_restriction R X Y NX NY hNX hNY U W f m hWU hWopen (hf m)).
have [D hD]:=norm_smooth_fields_exist hf.
exists W; split; first exact hWa.
split; first by move=>x hx; exact (hUA x (hWU x hx)).
split; first exact hfW.
exists (fun m=>D m a); split.
- move=>m.
  exact ((@norm_higher_differential_open_restriction R X Y NX NY hNX hNY Z ev ZN hZ m
    U W f hWU hWopen a hWa (D m a)).1 ((hD m).1 a ha)).
- move=>eps heps.
  have htwo:0<=(2:R) by rewrite ler0n.
  have [n hn]:=geometric_uniform_tail hq htwo heps.
  exists n.+1=>N hN; have hnN:(n<=N)%N:=leq_trans (leqnSn n) hN.
  case:N hN hnN=>[|k] hN hnN; first by [].
  move=>x hx.
  have hseg t (ht:0<=t<=1):U (a+t*:(x-a)).
    apply: hWU.
    rewrite /W addrAC subrr add0r (real_seminorm_scale hNX.1) (ger0_norm (andP ht).1).
    have hh:=ler_wpM2r (real_seminorm_nonnegative hNX.1 (x-a)) (andP ht).2.
    rewrite mul1r in hh; exact (le_lt_trans hh hx).
  have hcoef t (ht:0<=t<=1):
      NY (((k.+1)`!)%:R^-1 *: ev k.+1 [ffun j=>x-a] (D k.+1 (a+t*:(x-a))))<=q^+k.+1.
    pose y:=a+t*:(x-a).
    have hy:U y:=hseg t ht.
    have hd:has_norm_higher_differential NX ev ZN U f k.+1 y (D k.+1 y):=(hD k.+1).1 y hy.
    have hunit v (hv:NX v<=1):
        NY (((k.+1)`!)%:R^-1 *: ev k.+1 [ffun j=>v] (D k.+1 y))<=c^+k.+1.
      exact (hb k.+1 (leq0n k) y hy (D k.+1 y) hd v hv).
    have hh:=@normalized_diagonal_homogeneous_bound R k.+1 X Y (Z k.+1) NX NY hNX hNY
      (@ev k.+1) (@ZN k.+1) (hZ k.+1) (D k.+1 y) (c^+k.+1) hunit (x-a).
    rewrite -exprMn in hh.
    apply: le_trans hh _.
    have hcr:c*NX (x-a)<=q.
      have hh0:=ler_wpM2l hc (ltW hx).
      have hcrq:c*r<=q by rewrite /q mulrDl mul1r; lra.
      exact (le_trans hh0 hcrq).
    exact (lerXn2r k.+1 (mulr_ge0 hc (real_seminorm_nonnegative hNX.1 (x-a)))
      (ltW (andP hq).1) hcr).
  have hrem:=@norm_taylor_diagonal_remainder_bound R X Y NX NY hNX hNY Z ev ZN hZ
    U f D a (x-a) k (q^+k.+1) (fun i _=>(hD i).1) (hD k.+1).2 hseg hcoef.
  have htail:=hn k.+1 hnN.
  rewrite mulrC in htail.
  have hsum:=le_lt_trans hrem htail.
  have hshift:a+(x-a)=x by rewrite addrC subrK.
  rewrite hshift /norm_taylor_value in hsum.
  exact hsum.
Qed.
