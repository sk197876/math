(** Federer (1969), 3.2.46, pp. 281–282:
    frozen local coordinates and arbitrarily small two-sided
    distortion imply continuity of the actual nonnegative
    scalar quantity. This general-topology support lemma
    does not select a global frozen field. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra
  classical_sets topology.
From Federer Require Import RealMetricBackground NaturalPowerNearOne.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [local_multiplicative_continuity]: supporting
    continuity in the local-isometry argument of 3.2.46,
    pp. 281–282. At each point and each factor
    lambda>1, a genuine continuous frozen scalar agrees
    there and bounds the original scalar on an actual
    neighbourhood in both directions. Singular zero values
    are included without a strict-positivity hypothesis. *)
Theorem local_multiplicative_continuity (R : realType) (X : topologicalType)
    (F : X -> real_line_metric R) k :
  (forall x, 0<=F x) ->
  (forall a (lambda : R), 1<lambda ->
    exists Q : X -> real_line_metric R, continuous Q /\ Q a=F a /\
      nbhs a [set x | F x<=lambda^+k*Q x /\ Q x<=lambda^+k*F x]) ->
  continuous F.
Proof.
move=> hF hLocal a; apply/cvg_ballP=> e he.
have [lambda [hLambda [ht1 [ht2 hError]]]] :=
  @natural_power_factor_near_one R k (F a) e (hF a) he.
have [Q [hQ [hQa hNear]]] := hLocal a lambda hLambda.
have hEight : 0<(8:R) by rewrite ltr0n.
have he8 : 0<e/8 by rewrite divr_gt0.
have hQNear := @cvg_ball R (real_line_metric R) X (nbhs a) (nbhs_filter a)
  Q (Q a) (hQ a) (e/8) he8.
apply: (@filterS X (nbhs a) (nbhs_filter a) _ _ _ (filterI hNear hQNear))=> x [[hUpper hLower] hClose].
rewrite /= !real_line_ball_distance /= hQa in hClose *.
have /andP [hLow hHigh] : -(e/8)<F a-Q x<e/8 by rewrite -ltr_norml.
have hT0 : 0<=lambda^+k-1 by lra.
have hErrorSmall : (lambda^+k-1)*F a<e/4.
  have hcBound : F a<=F a+1 by rewrite lerDl.
  have hBound := ler_wpM2l hT0 hcBound.
  exact: le_lt_trans hBound hError.
have hCancel8 : (e/8)*8=e by rewrite divfK ?pnatr_eq0.
have hCancel4 : (e/4)*4=e by rewrite divfK ?pnatr_eq0.
rewrite ltr_norml; apply/andP; split; nra.
Qed.
