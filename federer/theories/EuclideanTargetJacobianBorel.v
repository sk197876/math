(** Federer (1969), 3.2.10, p. 248: the Jacobian
    integrand is measurable on its actual differential domain.
    Borel preimages follow from the exact differential graph
    and continuous exterior Jacobian, without a total default. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric NormDifferentialUP NormClassOneUP
  ContinuousOperatorUP ContinuousOperatorNorm EuclideanHomOperator HomSpaceNormTopology
  MetricProductBackground TopologicalProductMaps RealMetricBackground TopologicalBorel
  ContinuousBorelPreimages NormDifferentialBorelTests EuclideanLinearJacobian
  EuclideanTargetJacobianContinuity JacobianUP Jacobian PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_target_jacobian_borel_preimage]: the
    integrand of Federer 3.2.10, p. 248. Every Borel
    inverse image of J_n f is Borel where the actual
    differential exists; undefined points occur in no preimage. *)
Theorem euclidean_target_jacobian_borel_preimage (R:realType) m n
    (f:R_n R m->R_n R n):
  norm_class_zero (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f ->
  forall V:set (real_line_metric R),borel_set V ->
    @borel_set [the topologicalType of real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m))]
      (partial_function_preimage (euclidean_jacobian n setT f) V).
Proof.
move=>hf V hV.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose ev:=hom_of_linear (linear_id (Hom (R_n R m) (R_n R n))).
pose hZ:=@euclidean_hom_operator_space R m n.
pose E:=real_norm_metric_space hNX.
pose T:=real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ).
pose P:=metric_product E T.
pose C:set P:=fun p=>V (euclidean_linear_jacobian n p.2).
have hC:borel_set C.
  apply:(continuous_borel_preimage _ hV)=>p.
  exact (continuous_comp (@second_projection_continuous E T p)
    (@euclidean_target_jacobian_continuous R m n p.2)).
have [q [b hb]]:=@hom_space_finite_basis R (R_n R m) (R_n R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n).
have hTest:=@norm_differential_borel_domain_test R (R_n R m) (R_n R n) (Hom (R_n R m) (R_n R n))
  NX NY hNX hNY ev (@euclidean_operator_norm R m n) hZ m (@coordinate_basis R m)
  (@coordinate_basisP R m) q b hb setT f hf C hC.
have he:[set a:E|exists z,has_norm_differential NX NY setT f a (ev z) /\ C (a,z)]=
    partial_function_preimage (euclidean_jacobian n setT f) V.
  apply/seteqP; split=>a.
  - move=>[D [hD hVal]]; exists (euclidean_linear_jacobian n D); split; last exact hVal.
    apply:(euclidean_jacobian_graph n setT f a _).2; exists D; by split.
  - move=>[j [hj hVj]].
    have [D [hD hJ]]:=(euclidean_jacobian_graph n setT f a j).1 hj.
    exists D; split; first exact hD.
    by rewrite /C /= hJ.
by rewrite he in hTest.
Qed.
