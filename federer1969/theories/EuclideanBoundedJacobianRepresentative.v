(** Federer (1969), 3.2.38, p. 274: a bounded Borel scalar
    representative permits the actual Jacobian's Lebesgue-point argument.
    All auxiliary defaults leave its original partial domain unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  NormDifferentialUP LipschitzUP EuclideanLinearJacobian EuclideanJacobianBorelRepresentatives
  EuclideanJacobianUpperBound EuclideanJacobianMeasurable Jacobian
  BorelFunctionUP BorelFunctionBasic RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_bounded_top_jacobian_borel_representative]:
    supporting the two good-point conditions in Federer 3.2.38,
    p. 274. A local Borel representative is everywhere between zero
    and L^m and agrees at every actual differentiability point.
    Clipping only auxiliary values discharges the global bound rather
    than adding a bound or a derivative field as a theorem premise. *)
Theorem euclidean_bounded_top_jacobian_borel_representative (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (L:R):
  0<=L ->is_metric_lipschitz_bound setT f L ->
  exists J:inner_metric_space (@euclidean_inner_productP R m)->real_line_metric R,
    is_borel_function J /\(forall x,0<=J x<=L^+m) /\
    forall x D,has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT f x D ->
      J x=euclidean_linear_jacobian m D.
Proof.
move=>hL hBound.
have hLip:is_metric_lipschitz setT f.
  have hPositive:0<L+1 by apply:le_lt_trans hL _; rewrite ltrDl ltr01.
  exists (L+1); split; first exact:hPositive.
  split; first exact:ltW hPositive.
  move=>x y hx hy; apply:le_trans (hBound.2 x y hx hy) _.
  apply:ler_wpM2r; first exact:mdist_ge0; by rewrite lerDl ler01.
have [J0 [hBorel [hNonnegative hActual]]]:=
  @euclidean_top_jacobian_borel_representative_exists R m n f hLip.
pose clip:real_line_metric R->real_line_metric R:=fun y=>Num.min y (L^+m).
have hClip:continuous clip.
  move=>y; rewrite /clip.
  apply (@continuous_min R [the topologicalType of real_line_metric R]
    (fun y=>y) (fun _=>L^+m) y); [exact:cvg_id|exact:cvg_cst].
exists (clip \o J0); split.
- exact:borel_function_composition hBorel (continuous_borel_function hClip).
- split.
  + move=>x; rewrite /clip /= le_min ge_min lexx orbT andbT.
    by rewrite hNonnegative exprn_ge0.
  + move=>x D hD; rewrite /clip /= (hActual x D hD).
    apply:min_idPl; rewrite -lee_fin.
    apply:(@euclidean_jacobian_global_upper_bound R m n f L hL hBound x).
    exists (euclidean_linear_jacobian m D); split=>//.
    apply:(euclidean_jacobian_graph m setT f x _).2; exists D; by split.
Qed.
