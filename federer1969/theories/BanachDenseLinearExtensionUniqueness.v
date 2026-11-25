(** General normed-space background supporting Federer (1969),
    4.1.14, p. 371: a continuous linear extension is determined
    by its values on the original dense normal domain. The
    comparison allows different finite bounds and does not use
    completeness of either space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology lra ring.
From Federer Require Import Hom Bilinear RealNormUP NormMetric
  NormDifferentialUP NormBoundedLinearTopology BanachDenseLinearExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_dense_linear_extension_unique]: two
    bounded linear extensions that agree on the original dense
    domain are equal, supporting Federer 4.1.14, p. 371.
    Neither source nor target completeness is required. *)
Theorem bounded_dense_linear_extension_unique (R : realType)
    (A V W : lmodType R) (NV : V -> R) (NW : W -> R)
    (hNV : is_real_norm NV) (hNW : is_real_norm NW)
    (i : Hom A V) (F : Hom A W) (C D : R) (G H : Hom V W) :
  0 <= C -> 0 <= D -> is_norm_dense_linear_image NV i ->
  is_bounded_dense_linear_extension NV NW i F C G ->
  is_bounded_dense_linear_extension NV NW i F D H -> G=H.
Proof.
move=> hC hD hDense [hG hGBound] [hH hHBound].
apply: hom_ext => v; apply/eqP; rewrite -subr_eq0; apply/eqP.
apply: hNW.2.
have hNonnegative := real_seminorm_nonnegative hNW.1 (G v-H v).
have hZero : NW (G v-H v) <= 0.
  apply/ler_addgt0Pr => e he; rewrite add0r.
  have hDen : 0<C+D+1 by lra.
  pose d := e/(C+D+1).
  have hd : 0<d by rewrite /d divr_gt0.
  have [a ha] := hDense v d hd.
  have hFirst := hGBound (v-i a).
  have hSecond := hHBound (v-i a).
  rewrite (linB (hom_linear G)) (hG a) in hFirst.
  rewrite (linB (hom_linear H)) (hH a) in hSecond.
  have hEq : G v-H v = (G v-F a)-(H v-F a).
    by rewrite opprB addrA subrK.
  rewrite hEq.
  have hTriangle := @metric_triangle R (real_norm_metric_space hNW)
    (G v-F a) 0 (H v-F a).
  change (is_true (NW ((G v-F a)-(H v-F a)) <=
    NW (G v-F a-0)+NW (0-(H v-F a)))) in hTriangle.
  rewrite subr0 sub0r (real_seminorm_negate hNW.1) in hTriangle.
  have hN := real_seminorm_nonnegative hNV.1 (v-i a).
  have hCD : C+D <= C+D+1 by rewrite lerDl.
  have hIncrease := ler_wpM2r hN hCD.
  have hStrict : (C+D+1)*NV (v-i a)<e.
    by rewrite mulrC -ltr_pdivlMr.
  rewrite mulrDl in hIncrease; lra.
by apply/eqP; rewrite eq_le hZero hNonnegative.
Qed.

(** Source for [bounded_dense_linear_extension_continuous]: the
    extension bound gives the original norm topology continuity,
    supporting Federer 4.1.14, p. 371. *)
Lemma bounded_dense_linear_extension_continuous (R : realType)
    (A V W : lmodType R) (NV : V -> R) (NW : W -> R)
    (hNV : is_real_norm NV) (hNW : is_real_norm NW)
    (i : Hom A V) (F : Hom A W) (C : R) (G : Hom V W) :
  0 <= C -> is_bounded_dense_linear_extension NV NW i F C G ->
  continuous (fun v : real_norm_metric_space hNV =>
    (G v : real_norm_metric_space hNW)).
Proof.
move=> hC [_ hG]; apply: norm_bounded_linear_continuous.
by exists C.
Qed.
