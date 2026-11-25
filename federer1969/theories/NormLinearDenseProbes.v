(** Federer (1969), 3.1.2, p. 212: the final norm estimate in
    uniqueness of the approximate differential. Small nearby good
    directions force the bounded linear difference to vanish. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_linear_dense_probes_zero]: supporting last step of
    Federer 3.1.2, p. 212. The proof tests the sphere of radius r/2 and
    balls of radius e r with e<1/2, instead of the printed sphere of
    radius (1-e)r. The same triangle estimate and homogeneity force T=0;
    this formulation needs no chosen operator norm or attained supremum. *)
Theorem norm_linear_dense_probes_zero (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (T : Hom X Y) :
  norm_bounded_linear NX NY T ->
  (forall e : R, 0<e -> e<1/2 -> exists r : R, 0<r /\
    forall u, NX u=r/2 -> exists v, NX (u-v)<=e*r /\ NY (T v)<=e*r) ->
  T=0.
Proof.
move=> [C [hC hT]] hprobe.
have hC1 : 0<C+1 by lra.
have hunit : forall w, NX w= 1 -> NY (T w)=0.
  move=> w hw; apply/eqP; rewrite eq_le (real_seminorm_nonnegative hNY.1) andbT.
  rewrite leNgt; apply/negP=> hp.
  pose e := Num.min (1/4) (NY (T w)/(4*(C+1))).
  have hd : 0<4*(C+1) by rewrite mulr_gt0 // ltr0n.
  have he : 0<e.
    rewrite /e lt_min; apply/andP; split; first by lra.
    by rewrite divr_gt0.
  have he4 : e<= 1/4 by rewrite /e ge_min lexx.
  have heq : e<=NY (T w)/(4*(C+1)) by rewrite /e ge_min lexx orbT.
  have hem : e*(4*(C+1))<=NY (T w) by move: heq; rewrite ler_pdivlMr.
  have hehalf : e<1/2 by lra.
  have [r [hr hg]] := hprobe e he hehalf.
  have hr2 : 0<r/2 by rewrite divr_gt0 // ltr0n.
  have hu : NX ((r/2)*:w)=r/2.
    by rewrite (real_seminorm_scale hNX.1) (ger0_norm (ltW hr2)) hw mulr1.
  have [v [hv hTv]] := hg _ hu.
  have hi : T ((r/2)*:w)=T ((r/2)*:w-v)+T v.
    by rewrite -linearD /= subrK.
  have hb : NY (T ((r/2)*:w))<=C*(e*r)+e*r.
    rewrite hi; apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
    apply: lerD _ hTv; exact: le_trans (hT _) (ler_wpM2l hC hv).
  rewrite linearZ /= (real_seminorm_scale hNY.1) (ger0_norm (ltW hr2)) in hb.
  have hcancel : NY (T w)<=2*(C+1)*e by nra.
  nra.
apply: hom_ext=> x; rewrite hom_zeroE.
have [->|hx] := eqVneq x 0; first exact: linear0.
have hpos : 0<NX x by rewrite (real_norm_positive hNX.1 hNX.2).
have hnorm : NX ((NX x)^-1*:x)= 1.
  rewrite (real_seminorm_scale hNX.1) ger0_norm ?invr_ge0 ?ltW //.
  by rewrite mulVf // gt_eqF.
have hz := hunit _ hnorm.
rewrite linearZ /= (real_seminorm_scale hNY.1) ger0_norm ?invr_ge0 ?ltW // in hz.
have hzero : NY (T x)=0.
  move/eqP: hz; rewrite mulf_eq0 invr_eq0 (gt_eqF hpos) /=; exact/eqP.
exact: hNY.2 hzero.
Qed.
