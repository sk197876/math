(** Federer (1969), 4.1.2, p. 347: the actual norm Cauchy
    criterion used for coordinate derivatives with reflexive Banach
    targets. This supporting limit lemma uses only the given
    Banach completeness and the two-sided punctured real filter. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import RealMetricBackground RealMetricCompleteness
  RealCurveDerivativeUP RealNormUP NormMetric CompleteMetricUP NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [punctured_norm_cauchy_limit]: Cauchy's criterion
    for the norm limits defining D_j f, supporting the locally Lipschitz
    case of Federer 4.1.2, p. 347. Completeness provides an actual
    vector limit, with no finite-dimensional restriction. *)
Theorem punctured_norm_cauchy_limit (R : realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY)) (u : R -> Y) :
  (forall e : R, 0<e -> exists d : R, 0<d /\
    forall h k : R, 0<`|h|<d -> 0<`|k|<d -> NY (u h-u k)<e) ->
  exists v : Y, punctured_norm_limit NY u v.
Proof.
move=> hc.
pose M := real_line_metric R.
pose S : set M := [set h | h != 0].
have hcl : closure S (0 : M).
  move=> B /nbhs_ballP [d hd hB].
  have hd2 : 0<d/2 by rewrite divr_gt0 // ltr0n.
  exists (d/2); split; first by rewrite /S /= gt_eqF.
  apply: hB; change (`|0-d/2|<d).
  by rewrite sub0r normrN (ger0_norm (ltW hd2)); lra.
have PF : ProperFilter (within S (nbhs (0 : M))) := within_nbhs_proper hcl.
pose V:=real_norm_metric_space hNY.
pose f (h : M) : V := u h.
have PC : ProperFilter (f @ within S (nbhs (0 : M))) := fmap_proper_filter f PF.
have hC : cauchy (f @ within S (nbhs (0 : M))).
  apply/(@cauchyP _ _ _ PC)=> e he.
  have [d [hd hB]] := hc e he.
  have hd2 : 0<d/2 by rewrite divr_gt0 // ltr0n.
  have hh : 0<`|d/2|<d.
    rewrite (ger0_norm (ltW hd2)); apply/andP; split=> //; lra.
  exists (f (d/2)).
  change (nbhs (0 : M) [set h | S h -> ball (f (d/2)) e (f h)]).
  apply: (filterS _ (nbhsx_ballx (0 : M) d hd))=> h hball hS.
  change (NY (u (d/2)-u h)<e).
  apply: hB=> //; apply/andP; split; first by rewrite normr_gt0.
  by move: hball; change (`|0-h|<d -> `|h|<d); rewrite sub0r normrN.
have [v hv] := @hY _ PC hC.
exists v=> e he.
have hb : \forall h \near within S (nbhs (0 : M)), ball v e (f h).
  exact: (cvg_ballP _ _).1 hv e he.
rewrite near_withinE in hb.
have [d hd hB] := (nbhs_ballP _ _).1 hb.
exists d; split=> // h /andP [hh hhd].
have hball : ball (0 : M) d (h : M).
  change (`|0-h|<d); by rewrite sub0r normrN.
have hS : S h by rewrite /S /=; move: hh; rewrite normr_gt0.
have hvh := hB h hball hS.
move: hvh; change (NY (v-u h)<e ->NY (u h-v)<e).
by rewrite (real_seminorm_subtract hNY.1).
Qed.
