(** Federer (1969), 3.2.2, p. 242: the sets Z(s,i)
    are Borel, using the exact Borel graph of the differential
    and proved closed finite-radius tests. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP ContinuousOperatorUP ContinuousOperatorNorm EuclideanHomOperator
  HomSpaceNormTopology MetricProductBackground TopologicalBorel
  LinearModelLocus LinearModelBorelTests NormDifferentialBorelTests.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [linear_model_locus_borel]: the stated Borel
    property of Z(s,i), Federer 3.2.2, p. 242. Project
    the single-valued differential graph after imposing the
    closed vector and closed-ball remainder conditions. *)
Theorem linear_model_locus_borel (R:realType) m n
    (f:R_n R m->R_n R n) (s:Hom (R_n R m) (R_n R m)) lambda e i :
  norm_class_zero (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f ->
  @borel_set [the topologicalType of real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))]
    (linear_model_locus f s lambda e i).
Proof.
move=>hf.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose ev:=hom_of_linear (linear_id (Hom (R_n R m) (R_n R n))).
pose hZ:=@euclidean_hom_operator_space R m n.
pose P:=metric_product (real_norm_metric_space hNX)
  (real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ)).
pose C:set P:=fun p=>
  @linear_model_vector_test R (R_n R m) (R_n R n) (Hom (R_n R m) (R_n R n)) NX NY hNY ev
    (@euclidean_operator_norm R m n) hZ s (lambda^-1+e)%R (lambda-e)%R p.2 /\
  @linear_model_remainder_test R (R_n R m) (R_n R n) (Hom (R_n R m) (R_n R n)) NX NY hNX hNY ev
    (@euclidean_operator_norm R m n) hZ s f e (i.+1%:R:R)^-1 p.
have hC:closed C.
  exact (@linear_model_combined_test_closed R (R_n R m) (R_n R n) (Hom (R_n R m) (R_n R n))
    NX NY hNX hNY ev (@euclidean_operator_norm R m n) hZ s (lambda^-1+e)%R (lambda-e)%R
    f e (i.+1%:R:R)^-1 hf).
have [q [b hb]]:=@hom_space_finite_basis R (R_n R m) (R_n R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n).
have hTest:=@norm_differential_borel_domain_test R (R_n R m) (R_n R n) (Hom (R_n R m) (R_n R n))
  NX NY hNX hNY ev (@euclidean_operator_norm R m n) hZ m (@coordinate_basis R m)
  (@coordinate_basisP R m) q b hb setT f hf C (closed_borel_set hC).
exact hTest.
Qed.
