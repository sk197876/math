(** Federer (1969), 3.2.20, p. 256: public intrinsic
    approximate Jacobian. Use only the opaque partial-graph specification,
    with exact domain and nonnegative finite real values. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  PartialFunctionUP PartialFunctionPostcomposition ExtendedRealOrderTopology MeasureUP
  MeasureApproximateDifferentialUP PartialExteriorNormUP PartialExteriorNormLaws
  MeasureApproximateJacobianUP MeasureApproximateJacobianLaws MeasureApproximateJacobianSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_approximate_jacobian]: ap J_q f in
    Federer 3.2.20, p. 256, with exterior degree separated
    from measure-density dimension for 3.2.22, p. 258. The
    public object exposes neither an ambient differential nor the norm's
    supremum or graph implementation. *)
Definition measure_approximate_jacobian (R : realType) n k
    (phi : set (R_n R n) -> \bar R) m q
    (f : partial_function (R_n R n) (R_n R k)) :=
  @MeasureApproximateJacobians.value R n k phi m q f.

(** Source for [measure_approximate_jacobian_graph]: exact exterior-norm
    value relation in Federer 3.2.20, p. 256. Only the
    opaque specification of the chosen partial graph is used. *)
Lemma measure_approximate_jacobian_graph (R : realType) n k
    (phi : set (R_n R n) -> \bar R) m q
    (f : partial_function (R_n R n) (R_n R k)) a j :
  partial_function_graph (measure_approximate_jacobian phi m q f) a j <->
  has_measure_approximate_jacobian phi m q f a j.
Proof. exact: (@MeasureApproximateJacobians.laws R n k phi m q f a j). Qed.

(** Source for [measure_approximate_jacobian_domain]: actual approximate
    differentiability is exactly the domain required by "whenever" in
    Federer 3.2.20, p. 256. Degree zero does not add
    undefined points to that domain. *)
Theorem measure_approximate_jacobian_domain (R : realType) n k
    (phi : set (R_n R n) -> \bar R) m q
    (f : partial_function (R_n R n) (R_n R k)) :
  is_measure phi ->
  partial_function_domain (measure_approximate_jacobian phi m q f)=
    [set a | measure_approximately_differentiable_at (inner_norm (@euclidean_inner_productP R k))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) phi m f a].
Proof.
move=> hm; apply/seteqP; split.
- move=> a [j hj].
  apply: (@measure_approximate_jacobian_domain_iff R n k phi m q f a hm).1.
  exists j; exact: (measure_approximate_jacobian_graph _ _ _ _ _ _).1 hj.
- move=> a ha.
  have [j hj] := (@measure_approximate_jacobian_domain_iff R n k phi m q f a hm).2 ha.
  exists j; exact: (measure_approximate_jacobian_graph _ _ _ _ _ _).2 hj.
Qed.

(** Source for [measure_approximate_jacobian_nonnegative]: nonnegative
    exterior norm in Federer 3.2.20, p. 256. Each defined
    value is a finite real number by the norm-existence theorem. *)
Lemma measure_approximate_jacobian_nonnegative (R : realType) n k
    (phi : set (R_n R n) -> \bar R) m q
    (f : partial_function (R_n R n) (R_n R k)) a j :
  partial_function_graph (measure_approximate_jacobian phi m q f) a j -> 0<=j.
Proof.
move=> hj; have [d [_ hNorm]] := (measure_approximate_jacobian_graph _ _ _ _ _ _).1 hj.
exact: partial_exterior_norm_nonnegative hNorm.
Qed.

(** Source for [measure_approximate_jacobian_zero_degree_value]: the
    empty exterior power in the degree-zero instance of Federer 3.2.20,
    p. 256. Its value is one at each actual approximate
    differentiability point; the exact domain theorem remains unchanged. *)
Lemma measure_approximate_jacobian_zero_degree_value (R : realType) n k
    (phi : set (R_n R n) -> \bar R) m
    (f : partial_function (R_n R n) (R_n R k)) a j :
  partial_function_graph (measure_approximate_jacobian phi m 0 f) a j -> j= 1.
Proof.
move=> hj; have [d [_ hNorm]] := (measure_approximate_jacobian_graph _ _ _ _ _ _).1 hj.
exact: (partial_exterior_norm_unique hNorm (partial_exterior_norm_zero_degree d)).
Qed.

(** Source for [extended_measure_approximate_jacobian]: the finite
    approximate Jacobian embedded into the extended-real integral notation
    of Federer 3.2.20, pp. 256–257. Postcomposition preserves the
    exact partial domain; no zero extension is performed here. *)
Definition extended_measure_approximate_jacobian (R : realType) n k
    (phi : set (R_n R n) -> \bar R) m q
    (f : partial_function (R_n R n) (R_n R k)) :=
  partial_function_postcompose (measure_approximate_jacobian phi m q f)
    (fun j=>(j%:E : extended_real_line R)).
