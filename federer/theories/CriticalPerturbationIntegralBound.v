(** Federer (1969), 3.2.11, p. 249: the
    first integral estimate in the critical-rank perturbation.
    Derive the actual differential bound on every point of
    Q before applying the subset-integral comparison theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness EuclideanBlockLinearMaps EuclideanLebesgueDimensions
  CoareaCylinderFibres CoareaPerturbationMap CoareaPerturbationLinear CoareaPerturbationBound
  CoareaPerturbationDifferential CoareaJacobianMeasure CoareaIntegralUpperBound
  EuclideanTargetJacobianMeasurable Jacobian EuclideanLinearJacobian
  NormDifferentialUP NormDifferentialDirectional NormDifferentialLipschitzBound
  LipschitzUP MeasureUP MeasureIntegralUP MeasureSubsetIntegral PartialFunctionUP
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [critical_perturbation_source_integral_bound]:
    the upper estimate for the perturbed Jacobian integral
    in Federer 3.2.11, p. 249. Every x in A
    has an actual critical differential, and a proved global
    Lipschitz bound L controls it. No Jacobian bound or
    differentiability of the perturbation is an extra hypothesis. *)
Theorem critical_perturbation_source_integral_bound (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n.+1))
    L e (A:set (R_n R m)) (B:set (R_n R n.+1)):
  is_metric_lipschitz setT f ->is_metric_lipschitz_bound setT f L ->(0<e)%R ->
  measure_measurable (@euclidean_lebesgue_measure R (m+n.+1)) (coarea_cylinder A B) ->
  (forall x,A x ->exists D:Hom (R_n R m) (R_n R n.+1),
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n.+1)) setT f x D /\
    euclidean_linear_jacobian n.+1 D=0%R) ->
  euclidean_coarea_measure (coarea_perturbation_map f e) (coarea_cylinder A B)<=
    (e*(L+e)^+n)%R%:E*euclidean_lebesgue_measure (m+n.+1) (coarea_cylinder A B).
Proof.
move=>hf hGlobal he hQ hCritical.
pose X:=inner_metric_space (@euclidean_inner_productP R (m+n.+1)).
pose g:=fun w:X=>(coarea_perturbation_map f e w:
  inner_metric_space (@euclidean_inner_productP R n.+1)).
pose Q:=coarea_cylinder A B.
pose mu:=@euclidean_lebesgue_measure R (m+n.+1).
pose c:=(e*(L+e)^+n)%R.
have hLip:=@coarea_perturbation_map_lipschitz R m n.+1 f e hf (ltW he).
have hI:=euclidean_coarea_measure_integral hLip hQ.
have hPos:(0<L+e)%R by have hL:=hGlobal.1; lra.
have hc:(0<c)%R.
  rewrite /c; apply:mulr_gt0; first exact he.
  apply:exprn_gt0; exact hPos.
apply:(@coarea_subset_integral_upper_constant R [the choiceType of X] mu
  (euclidean_lebesgue_is_measure R (m+n.+1)) Q (extended_euclidean_target_jacobian g)
  (euclidean_coarea_measure g Q) c hQ hc _ hI)=>w j hw hJ.
have [D [hD hZero]]:=hCritical (@euclidean_first_block R m n.+1 w) hw.1.
have hDG:=@coarea_perturbation_differential R m n.+1 f e w D hD.
have hDNorm:forall v,(inner_norm (@euclidean_inner_productP R n.+1) (D v)<=
    L*inner_norm (@euclidean_inner_productP R m) v)%R.
  apply:(norm_differential_global_lipschitz_bound
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n.+1)) hD).
  move=>x y; exact (hGlobal.2 x y Logic.I Logic.I).
have [r [hr <-]]:=hJ.
have [M [hM hValue]]:=(euclidean_jacobian_graph n.+1 setT g w r).1 hr.
have hEq:M=coarea_perturbation_linear D e.
  exact (norm_differential_unique
    (inner_norm_real_norm (@euclidean_inner_productP R (m+n.+1)))
    (inner_norm_real_norm (@euclidean_inner_productP R n.+1)) hM hDG).
rewrite -hValue hEq lee_fin.
exact (coarea_critical_perturbation_jacobian_bound hGlobal.1 he hZero hDNorm).
Qed.
