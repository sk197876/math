(** Federer (1969), 3.1.13, p. 224:
    finite bounds for the derivatives of the
    compactly supported radial cutoff. This supporting
    compactness lemma works in arbitrary normed spaces. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric NormClassOneUP
  CompactFiniteCover MetricClosedBalls CompactNearbyUniformContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_class_zero_compact_bounded]:
    continuity on a compact set gives a
    finite norm bound, supporting the constants
    G_i for the bump derivatives in Federer
    3.1.13, p. 224. The target
    need not be finite dimensional or complete. *)
Theorem norm_class_zero_compact_bounded (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A K : set X) (f : X->Y) :
  compact [set x : real_norm_metric_space hNX | K x] ->
  K `<=` A -> norm_class_zero NX NY A f ->
  exists M : R, 0<M /\ forall x, K x -> NY (f x)<=M.
Proof.
move=>hK hKA hc.
have [d [hd hb]] := norm_class_zero_compact_uniform_nearby
  hNY hK hKA hc (@ltr01 R).
pose T := real_norm_metric_space hNX.
have hcover : K `<=` \bigcup_(c in K) [set y : T | mdist (c : T) y<d].
  move=>x hx; exists x=>//; by rewrite /= mdistxx.
have [F hFK hF] := @compact_open_finite_cover T T K
  (fun c=>[set y | mdist c y<d]) K hK
  (fun c _=>metric_open_ball_open c d) hcover.
pose S := \sum_(i : F) NY (f (val i)).
have hS : 0<=S by apply: sumr_ge0=>i _; exact: (real_seminorm_nonnegative hNY.1).
have hterm (i : F) : NY (f (val i))<=S.
  rewrite /S (bigD1 i) //= lerDl.
  apply: sumr_ge0=>j _; exact: (real_seminorm_nonnegative hNY.1).
exists (S+1); split; first by lra.
move=>x hx; have [c hcf hcx] := hF x hx.
have hkc := hFK c hcf.
have hdist : NX (x-c)<d.
  change (is_true (NX (c-x)<d)) in hcx.
  by rewrite (real_seminorm_subtract hNX.1).
have hsmall := hb c x (set_mem hkc) (hKA x hx) hdist.
have hn := hterm ([` hcf]%fset).
change (is_true (NY (f c)<=S)) in hn.
have ht := real_seminorm_triangle hNY.1 (f x-f c) (f c).
rewrite subrK in ht; lra.
Qed.
