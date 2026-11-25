(** General normed-space background for Federer (1969), 4.1.14,
    p. 371: the bounded linear map on the original dense normal
    domain extends to the complete flat space. The independent
    agreement and bound laws are proved from target completeness;
    the dense source need not carry a norm. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology lra ring.
From Federer Require Import Hom Bilinear RealNormUP NormMetric CompleteMetricUP
  BanachDenseLinearExtensionUP BanachDenseLimitConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section BanachDenseLinearExtension.
Variable R : realType.
Variables A V W : lmodType R.
Variables NV : V -> R.
Variables NW : W -> R.
Hypothesis hNV : is_real_norm NV.
Hypothesis hNW : is_real_norm NW.
Hypothesis hW : is_complete_metric_space (real_norm_metric_space hNW).
Variables i : Hom A V.
Variables F : Hom A W.
Variable C : R.
Hypothesis hC : 0 <= C.
Hypothesis hDense : is_norm_dense_linear_image NV i.
Hypothesis hBound : forall a, NW (F a) <= C * NV (i a).
Let G : V -> W := @dense_linear_limit R A V W NV NW hNV hNW hW
  i F C hC hDense hBound.
(** Source for [G_agrees]: the auxiliary extension agrees with
    every original value, supporting Federer 4.1.14, p. 371. *)
Let G_agrees a : G (i a) = F a.
Proof. exact: dense_linear_limit_extends. Qed.
(** Source for [G_lipschitz]: the auxiliary limit keeps the
    original bound, supporting Federer 4.1.14, p. 371. *)
Let G_lipschitz v w : NW (G v-G w) <= C*NV (v-w).
Proof. exact: dense_linear_limit_lipschitz. Qed.

(** Source for [dense_linear_limit_linear]: density passes the
    original linear identities to the complete target, the linear
    extension step in Federer 4.1.14, p. 371. *)
Lemma dense_linear_limit_linear : linear G.
Proof.
move=> a v w; apply/eqP; rewrite -subr_eq0; apply/eqP; apply: hNW.2.
have hNonnegative := real_seminorm_nonnegative hNW.1
  (G (a*:v+w)-(a*:G v+G w)).
have hZero : NW (G (a*:v+w)-(a*:G v+G w)) <= 0.
  apply/ler_addgt0Pr => e he; rewrite add0r.
  pose L := C+1.
  pose K := 2*L*(`|a|+1).
  have hL : 0<L by rewrite /L ltr_pwDr.
  have hA : 0<`|a|+1 by have := normr_ge0 a; lra.
  have hK : 0<K by rewrite /K !mulr_gt0 //; lra.
  pose d := e/K.
  have hd : 0<d by rewrite /d divr_gt0.
  have [p hp] := @hDense v d hd.
  have [q hq] := @hDense w d hd.
  pose b := `|a|*NV (v-i p)+NV (w-i q).
  have hb : 0<=b.
    apply: addr_ge0; last exact: real_seminorm_nonnegative hNV.1 _.
    exact: mulr_ge0 (normr_ge0 a) (real_seminorm_nonnegative hNV.1 _).
  have hbSmall : b<(`|a|+1)*d.
    have hScale := ler_wpM2l (normr_ge0 a) (ltW hp).
    rewrite /b mulrDl mul1r; lra.
  have hInput : NV (a*:v+w-i (a*:p+q)) <= b.
    rewrite (hom_linear i).
    have hEq : a*:v+w-(a*:i p+i q) = a*:(v-i p)+(w-i q).
      by rewrite scalerBr opprD addrACA.
    rewrite hEq; apply: le_trans (real_seminorm_triangle hNV.1 _ _) _.
    by rewrite (real_seminorm_scale hNV.1) /b.
  have hFirst := G_lipschitz (a*:v+w) (i (a*:p+q)).
  rewrite G_agrees in hFirst.
  have hFirstBound := le_trans hFirst (ler_wpM2l hC hInput).
  have hPv := G_lipschitz (i p) v.
  have hQw := G_lipschitz (i q) w.
  rewrite G_agrees (real_seminorm_subtract hNV.1 (i p) v) in hPv.
  rewrite G_agrees (real_seminorm_subtract hNV.1 (i q) w) in hQw.
  have hSecond : NW (F (a*:p+q)-(a*:G v+G w)) <= C*b.
    rewrite (hom_linear F).
    have hEq : a*:F p+F q-(a*:G v+G w) =
        a*:(F p-G v)+(F q-G w).
      by rewrite scalerBr opprD addrACA.
    rewrite hEq.
    have hTriangle := real_seminorm_triangle hNW.1
      (a*:(F p-G v)) (F q-G w).
    rewrite (real_seminorm_scale hNW.1) in hTriangle.
    have hScale := ler_wpM2l (normr_ge0 a) hPv.
    have hSum := lerD hScale hQw.
    apply: le_trans hTriangle (le_trans hSum _).
    by rewrite /b mulrDr mulrCA lexx.
  have hTriangle := @metric_triangle R (real_norm_metric_space hNW)
    (G (a*:v+w)) (F (a*:p+q)) (a*:G v+G w).
  change (is_true (NW (G (a*:v+w)-(a*:G v+G w)) <=
    NW (G (a*:v+w)-F (a*:p+q))+
    NW (F (a*:p+q)-(a*:G v+G w)))) in hTriangle.
  have hIncrease : 2*(C*b)<=2*(L*b).
    have hCL : C<=L by rewrite /L lerDl.
    have h := ler_wpM2r hb hCL.
    by lra.
  have hStrict : 2*(L*b)<2*(L*((`|a|+1)*d)).
    have hTwo : 0 < (2:R) by lra.
    by rewrite (ltr_pM2l hTwo) (ltr_pM2l hL).
  have hEnd : 2*(L*((`|a|+1)*d))=e.
    have hEq : 2*(L*((`|a|+1)*d))=K*d by rewrite /K !mulrA.
    rewrite hEq /d mulrC divfK; first by [].
    exact: lt0r_neq0 hK.
  rewrite hEnd in hStrict.
  have hTotal := le_trans hTriangle (lerD hFirstBound hSecond).
  have hTwice : C*b+C*b = 2*(C*b) by ring.
  rewrite hTwice in hTotal.
  exact: ltW (le_lt_trans (le_trans hTotal hIncrease) hStrict).
by apply/eqP; rewrite eq_le hZero hNonnegative.
Qed.

(** Source for [bounded_dense_linear_extension_exists]: bounded
    linear extension from the original dense normal subspace to
    a complete flat target, supporting Federer 4.1.14, p. 371.
    No source completeness, source norm or target separability is
    required. The bound is the original constant C. *)
Theorem bounded_dense_linear_extension_exists :
  exists H : Hom V W,
    is_bounded_dense_linear_extension NV NW i F C H.
Proof.
have hLinear := dense_linear_limit_linear.
pose H : Hom V W := @HomMap R V W G (introT (asboolP _) hLinear).
exists H; split; first exact: G_agrees.
move=> v.
have hZero : G 0=0.
  have h := G_agrees (0:A).
  by rewrite (lin0 (hom_linear i)) (lin0 (hom_linear F)) in h.
have h := G_lipschitz v 0.
by rewrite hZero !subr0 in h.
Qed.
End BanachDenseLinearExtension.
