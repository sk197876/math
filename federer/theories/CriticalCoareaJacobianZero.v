(** Federer (1969), 3.2.11, p. 249: on the
    critical source set, the actual target Jacobian is zero.
    Its zero extension has integral zero on any such set. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLebesgueDimensions EuclideanTargetJacobianMeasurable EuclideanLinearJacobian
  Jacobian NormDifferentialUP CoareaJacobianMeasure PartialFunctionUP PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureSubsetIntegral MeasureConullZeroIntegral MeasureDensityUP
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [critical_coarea_jacobian_measure_zero]:
    the left-hand zero integral in the critical case of
    Federer 3.2.11, p. 249. No finite-mass,
    measurability or extra differentiability hypothesis is added:
    the assumption states exactly the actual critical differential locus. *)
Lemma critical_coarea_jacobian_measure_zero (R:realType) m n
    (f:R_n R m->R_n R n) (A:set (R_n R m)):
  (forall x,A x ->exists D:Hom (R_n R m) (R_n R n),
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT f x D /\
    euclidean_linear_jacobian n D=0%R) ->
  euclidean_coarea_measure f A=0.
Proof.
move=>hCritical.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
pose u:=extended_euclidean_target_jacobian f.
pose cut:=partial_function_zero_extension (0:extended_real_line R) A u.
have hZero x:partial_function_graph cut x 0.
  case:(pselect (A x))=>hx.
  - apply:(@partial_function_zero_extension_on _ (extended_real_line R) 0 A u x 0 hx).2.
    exists 0%R; split; last by [].
    apply:(euclidean_jacobian_graph n setT f x 0%R).2.
    have [D [hD hZ]]:=hCritical x hx; exists D; by split.
  - exact ((@partial_function_zero_extension_off _ (extended_real_line R) 0 A u x 0 hx).2 (erefl _)).
have hIntegral:is_measure_integral mu cut 0.
  apply:(measure_almost_zero_integral hm).
  apply:(@measure_almost_everywhere_mono R [the choiceType of X] mu hm setT _ _
    (measure_almost_everywhere_true hm))=>x _; exact:hZero.
have hLaw:=euclidean_coarea_measure_laws f.
rewrite (hLaw A) /measure_subset_upper_integral.
exact (measure_upper_integral_unique (measure_upper_integral_specification mu cut) hIntegral.2.1).
Qed.
