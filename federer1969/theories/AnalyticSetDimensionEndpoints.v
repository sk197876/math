(** Federer (1969), 3.4.10, p. 337:
    global dimension lies between zero and the
    ambient dimension, including R^0. The whole space
    attains the upper endpoint. The empty-set value
    is only the documented auxiliary totalization. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness SetGermUP AnalyticVarietyGermUP AnalyticVarietyGermBooleanClosure
  AnalyticSetLocalDepth AnalyticSetDimension BoundedNaturalSupremumUP
  AnalyticManifoldSubsetDimension FunctionalAnalyticWhole FunctionalAnalyticManifold.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_set_dimension_bound]: the global
    supremum in 3.4.10, p. 337, is
    at most the original finite ambient dimension. *)
Lemma analytic_set_dimension_bound (R:realType) n (S:set (R_n R n)):
  (@analytic_set_dimension R n S<=n)%N.
Proof.
case:(pselect (S=set0))=>hEmpty.
- rewrite (@bounded_natural_supremum_empty (R_n R n) S
    (@analytic_set_local_depth R n S) (@analytic_set_dimension R n S)
    (@analytic_set_dimension_laws R n S) hEmpty);exact:leq0n.
- have [a [ha hValue]]:=@bounded_natural_supremum_attained (R_n R n) S
    (@analytic_set_local_depth R n S) (@analytic_set_dimension R n S)
    (@analytic_set_dimension_laws R n S) hEmpty.
  rewrite -hValue;exact:analytic_set_local_depth_bound.
Qed.

(** Source for [analytic_set_empty_dimension]: explicit empty-set
    totalization used at the endpoint of 3.4.10,
    p. 337; this assigns no dimension to
    the original empty variety germ. *)
Lemma analytic_set_empty_dimension (R:realType) n:
  @analytic_set_dimension R n set0=0%N.
Proof.
exact:(@bounded_natural_supremum_empty (R_n R n) set0 (@analytic_set_local_depth R n set0)
  (@analytic_set_dimension R n set0) (@analytic_set_dimension_laws R n set0) erefl).
Qed.

(** Source for [analytic_set_whole_dimension]: the whole
    Euclidean space, including R^0, has its original
    ambient dimension in 3.4.10, p. 337. *)
Lemma analytic_set_whole_dimension (R:realType) n:
  @analytic_set_dimension R n setT=n.
Proof.
have hLower:=@analytic_manifold_subset_dimension R n n setT setT 0
  (@analytic_variety_germ_whole R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) 0)
  (functional_analytic_submanifold_analytic (@functional_analytic_whole R n))
  Logic.I (fun _ _=>Logic.I).
apply/eqP;rewrite eqn_leq;apply/andP;split;[exact:analytic_set_dimension_bound|exact:hLower].
Qed.
