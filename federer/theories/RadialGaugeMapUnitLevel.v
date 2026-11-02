(** Federer (1969), 3.2.35, p. 271:
    the corrected radial map parametrizes the
    actual unit gauge level. Unit-sphere positivity
    is discharged from boundedness in the body theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import RealNormUP MinkowskiGaugeUP MinkowskiGaugeBasic MinkowskiGaugeHomogeneity
  RadialGaugeMapUP PartialFunctionUP PartialMetricLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radial_gauge_map_unit_level]: the
    image identity underlying the boundary display
    in Federer 3.2.35, p. 271, corrected
    by erratum p. 5, book p. 271 line 24.
    Homogeneity sends the original sphere to {g=1}.
    Normalize each unit-gauge point by its actual
    norm for the converse. The auxiliary positivity
    on the sphere will follow from the original
    bounded-body hypothesis, rather than being added
    to the final numbered theorem. *)
Theorem radial_gauge_map_unit_level (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (S:set V) (g:V->R) (f:partial_function V V):
  @is_minkowski_gauge R V S g ->S 0 ->@is_radial_gauge_map R V N g f ->
  (forall u:V,N u= 1 ->0<g u) ->partial_function_range f=[set y|g y= 1].
Proof.
move=>hG hZero hF hPositive; apply/seteqP; split=>y.
- move=>[u hu].
  have [hUnit hValue]:=(@radial_gauge_map_graph_law R V N g f hF u y).1 hu.
  have hPos:=hPositive u hUnit.
  have hInv:0<(g u)^-1 by rewrite invr_gt0.
  change (g y= 1); rewrite -hValue
    (@minkowski_gauge_positive_homogeneous R V S g hG (g u)^-1 u hInv).
  by rewrite mulVf ?gt_eqF.
- move=>hy.
  have hy0:y!=0.
    apply/negP=>/eqP he.
    have hG0:=@minkowski_gauge_zero R V S g hG hZero.
    change (g y= 1) in hy; rewrite he hG0 in hy.
    by move/eqP:hy; rewrite eq_sym oner_eq0.
  have hNorm:0<N y by rewrite (real_norm_positive hN.1 hN.2).
  have hNorm0:N y!=0 by rewrite gt_eqF.
  have hInv:0<(N y)^-1 by rewrite invr_gt0.
  pose u:V:=(N y)^-1*:y.
  have hUnit:N u= 1.
    by rewrite /u (real_seminorm_scale hN.1) (ger0_norm (ltW hInv)) (mulVf hNorm0).
  have hGauge:g u=(N y)^-1.
    rewrite /u (@minkowski_gauge_positive_homogeneous R V S g hG (N y)^-1 y hInv).
    by rewrite hy mulr1.
  exists u; apply:(@radial_gauge_map_graph_law R V N g f hF u y).2.
  split; first exact hUnit.
  by rewrite hGauge /u invrK scalerA (mulfV hNorm0) scale1r.
Qed.
