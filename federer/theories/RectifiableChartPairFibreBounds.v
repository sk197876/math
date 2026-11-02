(** Federer (1969), 3.2.22, p. 260: compare
    the Hausdorff masses of the actual source fibre
    and its parameter fibre by the two chart bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import LipschitzUP MetricBiLipschitzUP MetricBiLipschitzHausdorff
  HausdorffMeasure MappingMultiplicity RectifiableChartPairPieces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_chart_pair_fibre_mass_bounds]:
    the two Lipschitz fibre comparisons in Federer
    3.2.22, p. 260. The exact fibre identity
    and 2.10.11 give both inequalities, with d=m-mu
    in the application. Infinite masses and degree zero
    are retained; no fibre measurability is assumed here. *)
Lemma rectifiable_chart_pair_fibre_mass_bounds (R:realType)
    (X Y U V:metricType R) (K:set X) (C:set U)
    (psi:X->Y) (F:Y->V) (gamma:U->V) (G:V->U)
    (lambda:R) (x0:X) d y:
  is_metric_bilipschitz_bound K psi lambda ->
  (forall u,C u ->G (gamma u)=u) ->C y ->
  @hausdorff_measure R Y d
      (mapping_fibre F (rectifiable_chart_pair_piece K C psi F gamma) (gamma y))<=
    (lambda^+d)%R%:E* @hausdorff_measure R X d
      (mapping_fibre (fun a=>G (F (psi a))) (rectifiable_chart_pair_parameters K C psi F gamma) y) /\
  @hausdorff_measure R X d
      (mapping_fibre (fun a=>G (F (psi a))) (rectifiable_chart_pair_parameters K C psi F gamma) y)<=
    (lambda^+d)%R%:E* @hausdorff_measure R Y d
      (mapping_fibre F (rectifiable_chart_pair_piece K C psi F gamma) (gamma y)).
Proof.
move=>hBi hG hy.
pose A:=mapping_fibre (fun a=>G (F (psi a)))
  (rectifiable_chart_pair_parameters K C psi F gamma) y.
have hSub:A `<=` K by move=>a [[ha _] _].
have hBounds:=@metric_bilipschitz_hausdorff_bounds R X Y K psi lambda x0 d A hBi hSub.
have hFibre:=@rectifiable_chart_pair_fibre X Y U V K C psi F gamma G y hG hy.
by rewrite hFibre.
Qed.
