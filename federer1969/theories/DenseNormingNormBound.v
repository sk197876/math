(** Federer (1969), 2.9.22, p. 167: recover the norm from countably many
    dual evaluations in the separable case. This supporting equivalent bound
    uses unit norming functionals at a dense subset of Y; their finite
    absolute evaluations determine closed norm balls. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric SeparableClosedCover DenseNormingFunctionals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dense_norming_family_norm_bound]: supporting
    norm recovery in Federer 2.9.22, p. 167, the supremum
    display preceding the measurability observation. The chosen
    unit norming family gives N(y)<=r exactly when all its
    absolute evaluations on y are <=r. No supremum witness
    or finite-dimensional representation is exposed. *)
Theorem dense_norming_family_norm_bound (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R) (k : E -> D)
    (hk : is_dual_norming_family N ed DN k)
    (C : set (real_norm_metric_space hN)) :
  dense C -> forall y r, N y<=r <-> forall c, C c -> `|ed (k c) y|<=r.
Proof.
move=> hC y r; split.
  move=> hyr c _; exact: le_trans (dual_norming_family_bound hk c y) hyr.
move=> hB; rewrite leNgt; apply/negP=> hgap.
have he : 0<(N y-r)/4 by rewrite divr_gt0 // ?subr_gt0 // ltr0n.
have [c [hc hnear]] := metric_dense_point_near hC y he.
change (is_true (N (y-c)<(N y-r)/4)) in hnear.
have hb := dual_norming_family_bound hk c (c-y).
rewrite (linearB (hom_as_linear (ed (k c))) c y) !hom_as_linearE
  (real_seminorm_subtract hN.1 c y) in hb.
rewrite (dual_norming_family_value hk c) in hb.
have ht := ler_distD (ed (k c) y) (ed (k c) c) 0.
rewrite !subr0 (dual_norming_family_value hk c)
  (ger0_norm (real_seminorm_nonnegative hN.1 c)) in ht.
have hBc := hB c hc.
have hnorm := real_seminorm_triangle hN.1 (y-c) c.
rewrite subrK in hnorm.
by lra.
Qed.
