(** Federer (1969), 4.1.14, p. 371: the scalar
    affine weights of the two smooth approximations converge
    uniformly on the original compact support. Reuse
    continuity on a compact image, including degree zero
    and a vanishing majorant, rather than changing the weight. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground
  MetricProductBackground NormMetricContinuity NormMetricSubtractContinuity
  CompactWeightedImageUniform.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_affine_weight_uniform]: the actual
    weights |g_i-f_i|(sigma+eta_i)^m converge uniformly to
    |g-f|sigma^m on K, supporting the affine limit in
    Federer 4.1.14, p. 371. Uniform convergence and
    compactness concern only K; no nonempty-set premise,
    lower bound on sigma or whole-target bound is imposed. *)
Theorem current_affine_weight_uniform (R : realType) (A : choiceType)
    (Y : lmodType R) (NY : Y -> R) (hNY : is_real_norm NY)
    (K : set A) (f g : A -> Y) (a b : nat -> A -> Y)
    (sigma : A -> R^o) (eta : nat -> R) (m : nat) :
  compact ((fun x => ((g x,f x),sigma x)) @` K :
    set (metric_product
      (metric_product (real_norm_metric_space hNY) (real_norm_metric_space hNY))
      (real_line_metric R))) ->
  (forall eps:R, 0<eps -> exists N:nat, forall i:nat, (N<=i)%N ->
    forall x, K x -> NY (a i x-f x)<eps) ->
  (forall eps:R, 0<eps -> exists N:nat, forall i:nat, (N<=i)%N ->
    forall x, K x -> NY (b i x-g x)<eps) ->
  (forall eps:R, 0<eps -> exists N:nat, forall i:nat, (N<=i)%N ->
    `|eta i|<eps) ->
  forall eps:R, 0<eps -> exists N:nat, forall i:nat, (N<=i)%N ->
    forall x, K x ->
      `|NY (b i x-a i x)*(sigma x+eta i)^+m-
        NY (g x-f x)*(sigma x)^+m|<eps.
Proof.
move=> hImage hF hG hError.
pose YT := real_norm_metric_space hNY.
pose P := metric_product YT YT.
pose F (x:A) : P := (g x,f x).
pose G (i:nat) (x:A) : P := (b i x,a i x).
pose H (p:P) : R^o := NY (p.1-p.2).
have hH : continuous H.
  move=> p.
  exact: (@continuous_comp P YT (real_line_metric R)
    (fun p:P => p.1-p.2) (fun y:YT => NY y) p
    (@real_norm_metric_subtract_continuous R Y NY hNY p)
    (@real_norm_metric_norm_continuous R Y NY hNY (p.1-p.2))).
have hPair : forall eps:R, 0<eps -> exists N:nat,
    forall i:nat, (N<=i)%N -> forall x, K x -> mdist (G i x) (F x)<eps.
  move=> eps hEps.
  have [N hN] := hF eps hEps.
  have [M hM] := hG eps hEps.
  exists (maxn N M)=> i hi x hx.
  rewrite /G /F metric_product_distanceE gt_max.
  apply/andP; split.
  - exact: hM i (leq_trans (leq_maxr N M) hi) x hx.
  - exact: hN i (leq_trans (leq_maxl N M) hi) x hx.
exact: (@compact_weighted_image_uniform R A P K F G sigma eta H m
  hImage hH hPair hError).
Qed.
