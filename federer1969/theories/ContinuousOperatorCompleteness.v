(** Federer (1969), 3.1.1, p. 211: the continuous operator space
    Z is complete when X is finite dimensional and Y is complete.
    Basis evaluations give limits, interpolation represents the
    limiting operator, and the finite coordinate bound proves
    convergence in operator norm. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis BasisInterpolation
  NormFiniteLinearBound CompleteMetricUP MetricLipschitzCauchy
  ContinuousOperatorUP ContinuousOperatorNorm ContinuousOperatorEvaluation
  ContinuousOperatorFiniteCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_operator_complete]: completeness of
    Z in 3.1.1, p. 211, for arbitrary finite-dimensional normed X
    and complete normed Y. The proof also covers dimension zero. *)
Theorem continuous_operator_complete (R : realType) (X Y Z : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (evaluation : Hom Z (Hom X Y)) (ZN : Z -> R)
    (hZ : is_continuous_operator_space NX NY evaluation ZN)
    n (e : 'I_n -> X) (he : is_basis e) :
  is_complete_metric_space (real_norm_metric_space hNY) ->
  is_complete_metric_space (real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ)).
Proof.
move=> hY F PF hc.
pose hZN := continuous_operator_norm_is_norm hNY hZ.
pose E := real_norm_metric_space hZN.
pose T := real_norm_metric_space hNY.
pose ev i := fun z : E => (evaluation z (e i) : T).
have hi i : exists y : T, ev i @ F --> y.
  have PFi : ProperFilter (ev i @ F) := @fmap_proper_filter E T (ev i) F PF.
  apply: (hY _ PFi).
  apply: (@metric_lipschitz_cauchy_image R E T (ev i) (NX (e i)) F PF)=> //.
  - exact: real_seminorm_nonnegative hNX.1 _.
  - exact: continuous_operator_evaluation_distance.
pose y i := projT1 (cid (hi i)).
have hy i := projT2 (cid (hi i)).
pose L := hom_of_linear (@basis_interpolation R (Choice.clone 'I_n _) X Y e he (fun i => (y i : Y))).
have hL := @norm_finite_linear_bounded R X Y NX NY hNX hNY n e he L.
have [z hz] := continuous_operator_surjective hZ hL.
have hze i : evaluation z (e i)=y i by rewrite hz /L hom_of_linearE basis_interpolationE.
have [K [hK hbound]] := continuous_operator_finite_coordinate_bound hNX hNY hZ he.
have FF : Filter F := @filter_filter _ F PF.
exists z=> W hW.
have [r hr hb] := proj1 (metricType_numDomainType.nbhs_mdistP (z : E) W) hW.
have hd : 0 < r/(K+1) by apply: divr_gt0=> //; lra.
have hFi i : F [set w : E | NY (evaluation z (e i)-evaluation w (e i))<r/(K+1)].
  rewrite hze.
  have hball : nbhs (y i : T) [set v : T | NY (y i-v)<r/(K+1)].
    apply: (proj2 (metricType_numDomainType.nbhs_mdistP (y i : T) _)).
    exists (r/(K+1))=> //.
  exact: (hy i _ hball).
have hall := @filter_forall E (Finite.clone 'I_n _) _ F FF hFi.
apply: (@filterS _ F FF _ _ _ hall)=> w hw; apply: hb.
change (ZN (z-w)<r).
have hsmall : forall i, NY (evaluation (z-w) (e i))<=r/(K+1).
  move=> i; rewrite linearB /=; exact: ltW (hw i).
have hle := hbound (z-w) (r/(K+1)) (ltW hd) hsmall.
apply: le_lt_trans hle _.
have hprod : (K+1)*(r/(K+1))=r by rewrite mulrC divfK //; apply/eqP; lra.
nra.
Qed.
