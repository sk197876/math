(** Federer (1969), 3.2.47, p. 283: supporting a
    finite Lipschitz bound on a compact portion of the
    actual product coordinate domain. Class one and compactness
    prove this bound; no connectedness or global bound on
    the original open patch is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra.
From Federer Require Import Hom InnerProductUP InnerNorm InnerNormInequalities
  InnerMetric HilbertFormCompactness RealNormUP NormMetric HomeomorphismUP
  InnerOwnNormTopology NormClassOneUP NormCompactFunctionBound
  InnerClassOneLipschitzCover MetricCompactLocalLipschitz
  CoveringFamilyUP LipschitzUP LipschitzBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_class_one_compact_lipschitz]: class-one
    maps are Lipschitz on compact subsets of their original
    open domain, supporting H_e in 3.2.47, p. 283.
    The bound is proved from local derivative control and
    compact image bounds, in the original inner metrics. *)
Theorem inner_class_one_compact_lipschitz (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C)
    (A K:set V) (f:V->W):
  norm_class_one (inner_norm hB) (inner_norm hC) A f ->K `<=` A ->
  @compact (inner_metric_space hB) K ->
  @is_metric_lipschitz R (inner_metric_space hB) (inner_metric_space hC) K f.
Proof.
move=>[D hD] hKA hK.
pose X:=inner_metric_space hB.
pose Y:=inner_metric_space hC.
pose NX:=inner_norm hB.
pose NY:=inner_norm hC.
pose hNX:=inner_norm_real_norm hB.
pose hNY:=inner_norm_real_norm hC.
have hCompact:@compact (real_norm_metric_space hNX) K.
  have hImage:=continuous_compact
    (continuous_subspaceT (homeomorphism_continuous (inner_own_norm_homeomorphism hB))) hK.
  by rewrite image_id in hImage.
have [M [hM hBound]]:=@norm_class_zero_compact_bounded R V W NX NY hNX hNY
  A K f hCompact hKA (norm_class_one_zero hD).
apply:(@metric_compact_local_lipschitz R X Y K f (M+M) hK (addr_ge0 (ltW hM) (ltW hM))).
- move=>x y hx hy; rewrite inner_metric_distanceE.
  have hTriangle:=real_seminorm_triangle hNY.1 (f x) (-f y).
  rewrite (real_seminorm_negate hNY.1) in hTriangle.
  exact:(le_trans hTriangle (lerD (hBound x hx) (hBound y hy))).
- move=>c hc.
  have [U [hOpen [hcU [_ hLip]]]]:=@inner_class_one_local_lipschitz_patch R V W B C hB hC
    A f c (hKA c hc) (ex_intro _ D hD).
  have hNeighbour:nbhs (c:X) U.
    apply:open_nbhs_nbhs; by split.
  have [r hr hBall]:=(proj1 (metricType_numDomainType.nbhs_mdistP (c:X) U)) hNeighbour.
  have [L [_ hLocalBound]]:=hLip.
  exists r,L; split; first exact hr.
  exact:metric_lipschitz_bound_restrict hBall hLocalBound.
Qed.
