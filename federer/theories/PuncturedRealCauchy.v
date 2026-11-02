(** Federer (1969), 2.9.22, p. 167, Lipschitz case: "Cauchy's criterion
    implies" existence of all real dual derivatives. This supporting
    real-topology lemma proves the criterion for actual punctured limits
    from real completeness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import RealMetricBackground RealMetricCompleteness
  RealCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [punctured_real_cauchy_limit]: supporting real
    Cauchy criterion in Federer 2.9.22, p. 167. Pairwise
    small differences at all sufficiently small nonzero increments
    yield a finite punctured limit. Only the standard real
    completeness background is reused; no differentiation theorem
    is imported to prove this implication. *)
Theorem punctured_real_cauchy_limit (R : realType) (u : R -> R) :
  (forall e : R, 0<e -> exists d : R, 0<d /\
    forall h k : R, 0<`|h|<d -> 0<`|k|<d -> `|u h-u k|<e) ->
  exists v : R, punctured_real_limit u v.
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
pose f (h : M) : M := u h.
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
  change (`|u (d/2)-u h|<e).
  apply: hB=> //; apply/andP; split; first by rewrite normr_gt0.
  by move: hball; change (`|0-h|<d -> `|h|<d); rewrite sub0r normrN.
have [v hv] := @real_line_metric_complete R _ PC hC.
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
by move: hvh; change (`|v-u h|<e -> `|u h-v|<e); rewrite distrC.
Qed.
