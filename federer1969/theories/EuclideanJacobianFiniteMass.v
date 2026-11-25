(** Federer (1969), 3.2.38, pp. 274--275: the actual
    Jacobian integral is finite on every finite-mass measurable source. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanJacobianMeasurable EuclideanJacobianUpperBound JacobianDensityMeasure
  LipschitzUP MeasureUP MeasureBasic MeasureSubsetIntegral SubsetIntegralUpperConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_jacobian_finite_source_mass]: supporting
    the final finite-error squeeze in Federer 3.2.38, p. 275.
    The actual partial Jacobian is bounded by L^m at every graph
    point. Its existing subset integral and positive constant upper
    comparison prove finiteness on any measurable finite-mass A.
    No integrability, differentiability field or finite integral
    premise is added to the final compact-source theorem. *)
Lemma euclidean_jacobian_finite_source_mass (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  is_metric_lipschitz setT f ->measure_measurable (@euclidean_lebesgue_measure R m) A ->
  (@euclidean_lebesgue_measure R m A< +oo)%E ->(euclidean_jacobian_measure f A< +oo)%E.
Proof.
move=>hLip hA hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
have [L [hL hBound]]:=hLip.
have hPower:0<=L^+m:=exprn_ge0 _ (ltW hL).
have hIncrease:L^+m<L^+m+1 by rewrite ltrDl ltr01.
have hPositive:0<L^+m+1:=le_lt_trans hPower hIncrease.
have hIntegral:=euclidean_jacobian_measure_integral hLip hA.
have hCap:(euclidean_jacobian_measure f A<=(L^+m+1)%:E*mu A)%E.
  apply:(@subset_integral_positive_constant_upper_bound R X mu hm A
    (extended_euclidean_jacobian f) _ (L^+m+1) hA hPositive _ hIntegral).
  move=>x j hx hj.
  apply:le_trans (@euclidean_jacobian_global_upper_bound R m n f L (ltW hL) hBound x j hj) _.
  by rewrite lee_fin lerDl ler01.
have hMassFinite:mu A \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative hm A)).
apply:le_lt_trans hCap _.
rewrite -(fineK hMassFinite) -EFinM; exact:ltry.
Qed.
