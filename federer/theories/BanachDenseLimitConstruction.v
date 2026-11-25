(** General normed-space background for Federer (1969), 4.1.14,
    p. 371: bounded linear maps on the dense normal domain extend
    to complete flat spaces. This construction proves existence
    from Cauchy-filter completeness, 2.2.8, p. 64; it introduces
    no new axiom and assumes no norm on the dense source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology lra ring.
From Federer Require Import Hom Bilinear RealNormUP NormMetric CompleteMetricUP
  BanachDenseLinearExtensionUP BanachDenseApproximationFilter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section BanachDenseLimit.
Variable R : realType.
Variables A V W : lmodType R.
Variables NV : V -> R.
Variables NW : W -> R.
Hypothesis hNV : is_real_norm NV.
Hypothesis hNW : is_real_norm NW.
Local Notation X := (real_norm_metric_space hNV).
Local Notation Y := (real_norm_metric_space hNW).
Hypothesis hW : is_complete_metric_space Y.
Variables i : Hom A V.
Variables F : Hom A W.
Variable C : R.
Hypothesis hC : 0 <= C.
Hypothesis hDense : is_norm_dense_linear_image NV i.
Hypothesis hBound : forall a, NW (F a) <= C * NV (i a).
Local Notation AF := (dense_norm_approximation_filter NV i).
Let f : A -> Y := fun a => F a.

(** Source for [dense_linear_image_difference_bound]: the original
    bounded linear map in the extension step of Federer 4.1.14,
    p. 371, has the same bound on differences. *)
Lemma dense_linear_image_difference_bound a b :
  NW (F a - F b) <= C * NV (i a - i b).
Proof.
by rewrite -(linB (hom_linear F)) -(linB (hom_linear i)); exact: hBound.
Qed.

(** Source for [dense_linear_image_cauchy]: the bounded images
    of approximations to a point form a Cauchy filter, supporting
    Federer 4.1.14, p. 371. No topology on A is imposed. *)
Lemma dense_linear_image_cauchy (v : V) : cauchy (f @ AF v).
Proof.
have PF : ProperFilter (AF v) :=
  dense_norm_approximation_filter_proper hDense v.
apply/(@cauchyP R Y _ (fmap_proper_filter f PF)) => e he.
pose K := C + 1.
have hK : 0 < K by rewrite /K ltr_pwDr.
pose d := e / (2 * K).
have hd : 0 < d by rewrite /d divr_gt0 // mulr_gt0 // ltr0n.
have [a ha] := @hDense v d hd.
exists (f a); change (AF v [set b | ball (f a) e (f b)]).
exists d; split; first exact: hd.
move=> b hb; rewrite ballEmdist /=.
change (is_true (NW (F a - F b) < e)).
have hTriangle : NV (i a - i b) <= NV (v-i a) + NV (v-i b).
  have ht := @metric_triangle R X (i a) v (i b).
  change (is_true (NV (i a-i b) <= NV (i a-v)+NV (v-i b))) in ht.
  by rewrite (real_seminorm_subtract hNV.1 (i a) v) in ht.
have hFirst := dense_linear_image_difference_bound a b.
have hSecond := ler_wpM2l hC hTriangle.
have hThird : C * (NV (v-i a) + NV (v-i b)) <=
    K * (NV (v-i a) + NV (v-i b)).
  apply: ler_wpM2r; first exact: addr_ge0
    (real_seminorm_nonnegative hNV.1 _) (real_seminorm_nonnegative hNV.1 _).
  by rewrite /K; lra.
have hStrict : K * (NV (v-i a) + NV (v-i b)) < K * (2*d).
  rewrite (ltr_pM2l hK); lra.
have hEnd : K * (2*d) = e.
  by rewrite /d; field; apply: lt0r_neq0; lra.
rewrite hEnd in hStrict; exact: le_lt_trans (le_trans hFirst
  (le_trans hSecond hThird)) hStrict.
Qed.

(** Source for [dense_linear_limit_exists]: target completeness
    yields a limit of the original bounded images, the extension
    argument in Federer 4.1.14, p. 371. *)
Lemma dense_linear_limit_exists (v : V) :
  exists w : Y, f @ AF v --> w.
Proof.
apply: hW; first exact: fmap_proper_filter _
  (dense_norm_approximation_filter_proper hDense v).
exact: dense_linear_image_cauchy.
Qed.

(** Source for [dense_linear_limit]: auxiliary selection of the
    proved limit for the existence argument of Federer 4.1.14,
    p. 371. The public extension is sealed separately. *)
Definition dense_linear_limit (v : V) : Y :=
  projT1 (cid (dense_linear_limit_exists v)).

(** Source for [dense_linear_limit_converges]: the selected
    auxiliary limit is the actual image filter limit in the
    extension proof of Federer 4.1.14, p. 371. *)
Lemma dense_linear_limit_converges (v : V) :
  f @ AF v --> dense_linear_limit v.
Proof. exact: projT2 (cid (dense_linear_limit_exists v)). Qed.

(** Source for [dense_linear_limit_approximates]: simultaneous
    input and output approximation in the extension argument of
    Federer 4.1.14, p. 371. *)
Lemma dense_linear_limit_approximates (v : V) (e : R) : 0 < e ->
  exists a, NV (v-i a) < e /\ NW (dense_linear_limit v-F a) < e.
Proof.
move=> he.
have PF : ProperFilter (AF v) :=
  dense_norm_approximation_filter_proper hDense v.
have hNear := (proj1 (metricType_numDomainType.cvgrPdist_lt f
  (dense_linear_limit v)) (@dense_linear_limit_converges v)) e he.
have {}hNear := hNear (@filter_filter _ _ PF).
change (AF v [set a | NW (dense_linear_limit v-F a) < e]) in hNear.
have [d [hd hOutput]] := hNear.
have hRadius : 0 < Num.min e d by rewrite lt_min he hd.
have [a ha] := @hDense v _ hRadius.
have /andP [hae had] : (NV (v-i a) < e) && (NV (v-i a) < d).
  by rewrite -lt_min.
exists a; split; first exact: hae.
exact: hOutput a had.
Qed.

(** Source for [dense_linear_limit_extends]: the extension agrees
    with every original dense-source value, Federer 4.1.14,
    p. 371. Injectivity of the source map is not required. *)
Lemma dense_linear_limit_extends a : dense_linear_limit (i a) = F a.
Proof.
have PF : ProperFilter (AF (i a)) :=
  dense_norm_approximation_filter_proper hDense (i a).
have hFa : f @ AF (i a) --> (F a : Y).
  apply/metricType_numDomainType.cvgrPdist_lt => e he.
  change (AF (i a) [set b | NW (F a-F b) < e]).
  pose d := e/(C+1).
  have hDen : 0 < C+1 by rewrite ltr_pwDr.
  have hd : 0 < d by rewrite /d divr_gt0.
  exists d; split; first exact: hd.
  move=> b hb; apply: le_lt_trans (dense_linear_image_difference_bound a b) _.
  have hIncrease : C * NV (i a-i b) <= (C+1) * NV (i a-i b).
    apply: ler_wpM2r; first exact: real_seminorm_nonnegative hNV.1 _.
    by lra.
  apply: le_lt_trans hIncrease _.
  by rewrite mulrC -ltr_pdivlMr.
exact: (@cvg_unique Y (@metric_hausdorff R Y) _
  (fmap_proper_filter f PF) _ _ (@dense_linear_limit_converges (i a)) hFa).
Qed.

(** Source for [dense_linear_limit_lipschitz]: the extension
    keeps the original finite bound, Federer 4.1.14, p. 371.
    Only the target is complete. *)
Lemma dense_linear_limit_lipschitz (v w : V) :
  NW (dense_linear_limit v-dense_linear_limit w) <= C * NV (v-w).
Proof.
apply/ler_addgt0Pr => e he.
pose d := e/(2*(C+1)).
have hDen : 0 < 2*(C+1).
  by rewrite mulr_gt0 ?ltr0n // ltr_pwDr.
have hd : 0 < d by rewrite /d divr_gt0.
have [a [hva hFa]] := dense_linear_limit_approximates v hd.
have [b [hwb hFb]] := dense_linear_limit_approximates w hd.
have h1 := @metric_triangle R Y (dense_linear_limit v) (F a)
  (dense_linear_limit w).
have h2 := @metric_triangle R Y (F a) (F b) (dense_linear_limit w).
have h3 := dense_linear_image_difference_bound a b.
have h4 : NV (i a-i b) <= NV (v-w)+2*d.
  have ht1 := @metric_triangle R X (i a) v (i b).
  have ht2 := @metric_triangle R X v w (i b).
  change (is_true (NV (i a-i b) <= NV (i a-v)+NV (v-i b))) in ht1.
  change (is_true (NV (v-i b) <= NV (v-w)+NV (w-i b))) in ht2.
  rewrite (real_seminorm_subtract hNV.1 (i a) v) in ht1.
  have hSum : NV (v-i a)+NV (w-i b)<=2*d.
    have hTwo : 2*d=d+d by ring.
    rewrite hTwo; exact: lerD (ltW hva) (ltW hwb).
  have hChain := lerD (lexx (NV (v-i a))) ht2.
  rewrite addrCA in hChain.
  exact: le_trans (le_trans ht1 hChain) (lerD (lexx (NV (v-w))) hSum).
have h5 : C*NV (i a-i b) <= C*NV (v-w)+2*(C*d).
  apply: le_trans (ler_wpM2l hC h4) _.
  by rewrite mulrDr mulrCA lexx.
have hCp : 0<C+1 by rewrite ltr_pwDr.
have hEnd : 2*d+2*(C*d)=e.
  by rewrite /d; field; exact: lt0r_neq0 hCp.
change (is_true (NW (dense_linear_limit v-dense_linear_limit w) <=
  NW (dense_linear_limit v-F a)+NW (F a-dense_linear_limit w))) in h1.
change (is_true (NW (F a-dense_linear_limit w) <=
  NW (F a-F b)+NW (F b-dense_linear_limit w))) in h2.
rewrite (real_seminorm_subtract hNW.1 (dense_linear_limit w) (F b)) in hFb.
have hSum : NW (dense_linear_limit v-F a)+NW (F b-dense_linear_limit w)<=2*d.
  have hTwo : 2*d=d+d by ring.
  rewrite hTwo; exact: lerD (ltW hFa) (ltW hFb).
have hTotal := le_trans h1 (lerD (lexx (NW (dense_linear_limit v-F a))) h2).
rewrite addrCA in hTotal.
have hMiddle := le_trans h3 h5.
have hFinal := le_trans hTotal (lerD hMiddle hSum).
by rewrite -addrA [2*(C*d)+2*d]addrC hEnd in hFinal.
Qed.
End BanachDenseLimit.
