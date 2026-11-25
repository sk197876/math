(** Federer (1969), 3.1.11, p. 220:
    completeness of the continuous operator space. A Cauchy
    filter with pointwise limits converges uniformly after
    weighting by the input norm; no finite basis is needed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormOperatorNormUP
  ContinuousOperatorUP ContinuousOperatorNorm ContinuousOperatorEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_operator_cauchy_uniform]:
    the uniform operator-norm limit supporting the Banach
    space of endomorphisms in Federer 3.1.11, p. 220.
    The assertion holds for any normed source, and treats
    zero input vectors without division by their norm. *)
Theorem continuous_operator_cauchy_uniform (R : realType)
    (X Y Z : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (evaluation : Hom Z (Hom X Y)) (ZN : Z->R)
    (hZ : is_continuous_operator_space NX NY evaluation ZN)
    (F : set_system (real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ)))
    (g : X->Y) (PF : ProperFilter F) :
  cauchy F ->
  (forall x, (fun u=> (evaluation u x : real_norm_metric_space hNY)) @ F -->
    (g x : real_norm_metric_space hNY)) ->
  forall e : R, 0<e -> exists2 U, F U &
    forall u, U u -> forall x, NY (evaluation u x-g x)<=e*NX x.
Proof.
move=> hc hg e he.
pose E := real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ).
pose T := real_norm_metric_space hNY.
have FF : Filter F := @filter_filter _ F PF.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have [c hcB] := proj1 (@cauchyP R E F PF) hc (e/2) he2.
exists (ball c (e/2))=> // u hu x.
apply/ler_addgt0Pr=> d hd.
have hnb : nbhs (g x : T) [set y : T | mdist (g x : T) y<d].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (g x : T) _)).
  by exists d=> // y hy.
have hF := hg x _ hnb.
have [w [hw hgw]] := @filter_ex E F PF _ (@filterI E F FF _ _ hcB hF).
have huw : mdist (u : E) w<e.
  move: hu hw; rewrite !ballEmdist /= => h1 h2.
  apply: le_lt_trans (metric_triangle u c w) _.
  rewrite metric_sym (splitr e); exact: ltrD h1 h2.
have hvw : NY (evaluation u x-evaluation w x)<=e*NX x.
  have hh := @continuous_operator_evaluation_distance R X Y Z NX NY hNY
    evaluation ZN hZ x u w.
  change (is_true (NY (evaluation u x-evaluation w x)<=NX x*mdist (u:E) w)) in hh.
  apply: le_trans hh _; rewrite [e*NX x]mulrC.
  have hmul := ler_wpM2l (real_seminorm_nonnegative hNX.1 x) (ltW huw).
  exact hmul.
have hwg : NY (evaluation w x-g x)<d.
  change (is_true (NY (g x-evaluation w x)<d)) in hgw.
  by rewrite (real_seminorm_subtract hNY.1).
have hid : evaluation u x-g x=
    (evaluation u x-evaluation w x)+(evaluation w x-g x).
  by rewrite addrA subrK.
rewrite hid; apply: ltW; apply: le_lt_trans (real_seminorm_triangle hNY.1 _ _) _.
exact: ler_ltD hvw hwg.
Qed.
