(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets lra
  reals constructive_ereal topology.
From mathcomp.analysis.normedtype_theory Require Import normed_module.
From Federer Require Import RealMetricBackground NormMetricScaleContinuity MetricPairDistance
  BoundedSupportContinuous FunctionLatticeUP CoveringFamilyUP MetricBoundedUnion
  MetricClosedBalls CoveringFamilyLaws MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [bounded_set_unit_test_exists]: supporting metric
    cutoff for the converse class-M characterisation in Federer
    2.9.10, p. 157. A bounded set admits a continuous bounded
    test with bounded support, values in [0,1], and value one
    on the set. A radial cutoff proves existence; it requires
    neither compactness of bounded sets nor local compactness. *)
Theorem bounded_set_unit_test_exists (R : realType) (X : metricType R) (A : set X) :
  metric_set_bounded A -> exists f : X -> R,
    positive_function_lattice (@bounded_support_continuous_functions R X) f /\
    (forall x, A x -> f x = 1).
Proof.
move=> hA; case: (pselect (A !=set0))=> [[a ha]|hzero].
- have [r [hr hAr]] := @metric_bounded_distance_bound R X A a hA.
  pose f x := Num.min 1 (Num.max (r+1-mdist a x) 0).
  have hf0 x : 0<=f x by rewrite /f le_min ler01 le_max lexx orbT.
  have hdcont : continuous (fun x : X => (mdist a x : real_line_metric R)).
    apply: (@metric_fixed_lipschitz_continuous R X (real_line_metric R) _ 1 ler01)=> x y.
    change (`|mdist a x-mdist a y|<=1*mdist x y).
    have h := metric_pair_distance_change_bound a x a y.
  rewrite mdistxx add0r in h; by rewrite mul1r.
  exists f; split.
  + split; last exact hf0.
    split.
    * move=> x; apply: (@continuous_min R X (fun _ => 1) (fun z => Num.max (r+1-mdist a z) 0) x).
      -- exact: cvg_cst.
      -- apply: (@continuous_max R X (fun z => r+1-mdist a z) (fun _ => 0) x).
         ++ apply: (@continuousB R R^o X (fun _ => r+1) (fun z => mdist a z) x).
            ** exact: cvg_cst.
            ** exact: hdcont.
         ++ exact: cvg_cst.
    * split.
      -- exists 1=> x; by rewrite (ger0_norm (hf0 x)) /f ge_min lexx.
      -- apply: le_lt_trans (extended_metric_diameter_mono _)
           (@covering_closed_ball_bounded R X a (r+1) ltac:(lra)).
         move=> x /= hx.
         have hp : 0<f x.
           rewrite lt_neqAle (hf0 x) andbT; by rewrite eq_sym.
         move: hp; rewrite /f lt_min=> /andP [_].
         rewrite lt_max ltxx orbF subr_gt0=> hp; exact: ltW hp.
  + move=> x hx; rewrite /f min_l // le_max.
    apply/orP; left; have hd := hAr x hx; lra.
- exists (fun _ => 0); split.
  + split; first exact: bounded_support_continuous_zero.
    by move=> x.
  + move=> x hx; exfalso; apply: hzero; by exists x.
Qed.
