(** Federer (1969), 3.2.12, p. 250: the
    bounded target-degree Jacobian preserves the finite signed
    variation during characteristic approximation. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness LipschitzUP NormDifferentialLipschitzBound LinearJacobianSandwich
  Jacobian EuclideanTargetJacobianMeasurable EuclideanRectangularAdjoint CoareaLinearDuality CoareaAdjointBound
  PartialFunctionUP PartialFunctionPostcomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_target_jacobian_global_upper_bound]:
    J_n Df<=L^n in the signed reduction of Federer
    3.2.12, p. 250, by 1.7.6 and the
    differential Lipschitz bound. Includes n=0 and all actual
    Jacobian graph points, with no total derivative extension. *)
Lemma euclidean_target_jacobian_global_upper_bound (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (L:R):
  (0<=L)%R ->is_metric_lipschitz_bound setT f L ->
  forall x j,partial_function_graph (extended_euclidean_target_jacobian f) x j ->j<=(L^+n)%:E.
Proof.
move=>hL hLip x j [r [hr <-]].
have [D [hD hrJ]]:=(euclidean_jacobian_graph n setT f x r).1 hr.
have hUpper:forall v,(inner_norm (@euclidean_inner_productP R n) (D v)<=
    L*inner_norm (@euclidean_inner_productP R m) v)%R.
  apply:(@norm_differential_global_lipschitz_bound R _ _ _ _
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) f x D L hD).
  move=>z w; exact (hLip.2 z w Logic.I Logic.I).
have hAdj:=euclidean_rectangular_adjoint_bound hL hUpper.
have hLower v:(0%R*inner_norm (@euclidean_inner_productP R n) v<=
    inner_norm (@euclidean_inner_productP R m) (euclidean_rectangular_adjoint D v))%R.
  rewrite mul0r; exact:inner_norm_nonnegative.
have hBound:=(euclidean_top_jacobian_sandwich (lexx 0%R) hL hLower hAdj).2.
rewrite -hrJ lee_fin euclidean_target_jacobian_adjoint.
exact hBound.
Qed.
