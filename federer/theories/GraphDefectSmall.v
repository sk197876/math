(** Federer (1969), 3.1.23, p. 237: the small
    graph correction and its differential on sufficiently small balls. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  NormClassOneUP NormDifferentialConvexBound NormConvexHullDiameter GraphDefectCalculus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [graph_defect_small]: the two estimates
    |p*(z)-psi(z)|<=epsilon|z| and |p*-Dpsi(z)|<=epsilon
    in Federer 3.1.23, p. 237, with the
    translations at b retained. Derivative continuity gives
    the uniform bound and the convex increment theorem gives
    the value bound. Contractivity of p transfers both to
    the ambient ball, including its boundary. *)
Theorem graph_defect_small (R:realType) (X Z:lmodType R)
    (NX:X->R) (NZ:Z->R) (hNX:is_real_norm NX) (hNZ:is_real_norm NZ)
    (V:Z->Prop) (psi G:Z->X) (P:Hom X Z) (J:Hom Z X)
    (D:Z->Hom Z X) b eps :
  (forall z,G z=J z-psi z+(b-J (P b))) ->
  is_norm_class_one_field NZ NX V psi D ->
  has_norm_differential NZ NX V psi (P b) J -> psi (P b)=b ->
  (forall v,NZ (P v)<=NX v) -> 0<eps ->
  exists delta:R,0<delta /\ forall x,NX (x-b)<=delta ->
    V (P x) /\ NX (G (P x))<=eps*NX (x-b) /\
      forall v,NX ((J-D (P x)) (P v))<=eps*NX v.
Proof.
move=>hG hF hBase hpsib hP heps.
have hbV:=norm_domain_interior_member hNZ (norm_differential_interior hBase).
have hDb:D (P b)=J:=norm_differential_unique hNZ hNX
  (norm_class_one_differential hF hbV) hBase.
have hJ:=norm_differential_bounded hBase.
have [r [hr hVr]]:=norm_differential_interior hBase.
have [s [hs hDs]]:=norm_class_one_continuity hF hbV heps.
pose delta:=Num.min r s/2.
have hmin:0<Num.min r s by rewrite lt_min hr hs.
have hd:0<delta by rewrite /delta divr_gt0 // ltr0n.
have hdr:delta<r.
  have hh:delta<Num.min r s by rewrite /delta; lra.
  apply: lt_le_trans hh _; by rewrite ge_min lexx.
have hds:delta<s.
  have hh:delta<Num.min r s by rewrite /delta; lra.
  apply: lt_le_trans hh _; by rewrite ge_min lexx orbT.
pose U:=fun z=>NZ (z-P b)<=delta.
have hcontrol z (hz:U z):V z /\ forall v,NX ((J-D z) v)<=eps*NZ v.
  have hshift:P b+(z-P b)=z by rewrite addrC subrK.
  have hzV:V z.
    have hh:=hVr (z-P b) (le_lt_trans hz hdr); by rewrite hshift in hh.
  split; first exact hzV.
  move=>v.
  have hVz:V (P b+(z-P b)) by rewrite hshift.
  have hh:=hDs (z-P b) hVz (le_lt_trans hz hds) v.
  rewrite hshift hDb in hh.
  change (is_true (NX (J v-D z v)<=eps*NZ v)).
  rewrite (real_seminorm_subtract hNX.1).
  exact hh.
have hder z (hz:U z):exists L:Hom Z X,
    has_norm_differential NZ NX V G z L /\ forall v,NX (L v)<=eps*NZ v.
  exists (J-D z); split; last exact (hcontrol z hz).2.
  exact (graph_defect_differential hNZ hNX hG hJ
    (norm_class_one_differential hF (hcontrol z hz).1)).
have hbound:=@norm_differential_convex_bound R Z X NZ NX hNZ hNX V U G eps
  (@norm_ball_inner_convex R Z NZ hNZ (P b) delta) (ltW heps) hder.
have hbU:U (P b) by rewrite /U subrr (real_seminorm_zero hNZ.1); exact: ltW hd.
have hG0:G (P b)=0:=graph_defect_base_zero hG hpsib.
exists delta; split; first exact hd.
move=>x hx.
have hxU:U (P x).
  rewrite /U -linearB; exact (le_trans (hP (x-b)) hx).
split; first exact (hcontrol (P x) hxU).1.
split.
- have hh:=hbound (P x) (P b) hxU hbU.
  rewrite hG0 subr0 -linearB in hh.
  apply: le_trans hh _; exact (ler_wpM2l (ltW heps) (hP (x-b))).
- move=>v; apply: le_trans ((hcontrol (P x) hxU).2 (P v)) _.
  exact (ler_wpM2l (ltW heps) (hP v)).
Qed.
