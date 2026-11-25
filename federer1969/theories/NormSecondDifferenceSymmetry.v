(** Federer (1969), 3.1.11, p. 219:
    the quadratic four-point estimate forces symmetry
    of the candidate bilinear second differential. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom RealNormUP NormSecondDifferenceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_quadratic_second_remainder_symmetric]:
    the corollary that D^2 f(a) is symmetric, Federer
    3.1.11, p. 219. Once the preceding four-point
    limit holds, scaling fixed increments and exchanging
    them forces equality of the bilinear values. *)
Theorem norm_quadratic_second_remainder_symmetric (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (f : X->Y) (a : X) (B : Hom X (Hom X Y)) :
  has_norm_quadratic_second_remainder NX NY f a B ->
  forall u v, B v u=B u v.
Proof.
move=> hrem u v.
pose P := NX u+NX v.
pose Q := NY (B v u-B u v).
have hu0 := real_seminorm_nonnegative hNX.1 u.
have hv0 := real_seminorm_nonnegative hNX.1 v.
have hP : 0<=P by rewrite /P; exact: addr_ge0.
have hQ0 : 0<=Q := real_seminorm_nonnegative hNY.1 _.
have hQ : Q= 0.
  apply/eqP; apply/negPn/negP=> hnQ.
  have hQp : 0<Q by rewrite lt_def hnQ hQ0.
  have hP2 : 0<=P^+2 by rewrite exprn_ge0.
  have hden : 0< 4*P^+2+1 by nra.
  pose e := Q/(4*P^+2+1).
  have he : 0<e by rewrite /e divr_gt0.
  have heq : e*(4*P^+2+1)=Q by rewrite /e divfK // gt_eqF.
  have [d [hd hb]] := hrem e he.
  pose t := d/(2*(P+1)).
  have hden2 : 0< 2*(P+1) by nra.
  have ht : 0<t by rewrite /t divr_gt0.
  have hteq : t*(2*(P+1))=d by rewrite /t divfK // gt_eqF.
  have htP : t*P<d by nra.
  have htu : NX (t*:u)<d.
    rewrite (real_seminorm_scale hNX.1) (ger0_norm (ltW ht)).
    have hh : NX u<=P by rewrite /P; lra.
    exact: le_lt_trans (ler_wpM2l (ltW ht) hh) htP.
  have htv : NX (t*:v)<d.
    rewrite (real_seminorm_scale hNX.1) (ger0_norm (ltW ht)).
    have hh : NX v<=P by rewrite /P; lra.
    exact: le_lt_trans (ler_wpM2l (ltW ht) hh) htP.
  have h1 := hb (t*:u) (t*:v) htu htv.
  have h2 := hb (t*:v) (t*:u) htv htu.
  rewrite (norm_second_difference_symmetric f a (t*:v) (t*:u)) in h2.
  rewrite !(real_seminorm_scale hNX.1) (ger0_norm (ltW ht)) -mulrDr in h1.
  rewrite !(real_seminorm_scale hNX.1) (ger0_norm (ltW ht)) -mulrDr in h2.
  rewrite [NX v+NX u]addrC in h2.
  pose q := norm_second_difference f a (t*:u) (t*:v).
  pose b1 := B (t*:v) (t*:u).
  pose b2 := B (t*:u) (t*:v).
  have hid : (q-b2)-(q-b1)=b1-b2.
    have hh := @linear_remainder_difference_identity Y q 0 b2 q b1.
    rewrite !subr0 subrr sub0r in hh.
    by rewrite [RHS]opprB in hh.
  have htri := real_seminorm_triangle hNY.1 (q-b2) (-(q-b1)).
  rewrite (real_seminorm_negate hNY.1) hid in htri.
  have hbd : NY (b1-b2)<= 2*e*(t*P)^+2.
    apply: le_trans htri _.
    have hh := lerD h2 h1.
    change (is_true (NY (q-b2)+NY (q-b1)<=e*(t*P)^+2+e*(t*P)^+2)) in hh.
    have heq2 : e*(t*P)^+2+e*(t*P)^+2= 2*e*(t*P)^+2 by ring.
    by rewrite heq2 in hh.
  have hscale : b1-b2=(t^+2)*:(B v u-B u v).
    rewrite /b1 /b2 !linearZ /= ?hom_scaleE !linearZ /= !scalerA.
    by rewrite -scalerDr expr2.
  rewrite hscale (real_seminorm_scale hNY.1)
    (ger0_norm (exprn_ge0 2 (ltW ht))) in hbd.
  have heq2 : 2*e*(t*P)^+2=(t^+2)*(2*e*P^+2) by ring.
  rewrite heq2 in hbd.
  have ht2 : 0<t^+2 := exprn_gt0 2 ht.
  have hbQ : Q<= 2*e*P^+2 by move: hbd; rewrite ler_pM2l.
  nra.
apply/eqP; rewrite -subr_eq0; apply/eqP.
exact: hNY.2 _ hQ.
Qed.
