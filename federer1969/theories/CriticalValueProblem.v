(** Federer (1969), 3.4.1, p. 310: the critical-value problem.
    These predicates state the problem; 3.4.3 and 3.4.4 must prove its
    upper bound and sharpness. They introduce no existence assumption. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness RealNormUP NormMetric NormDifferentialUP NormRegularity
  RealHausdorffMeasure CriticalValueDegree CriticalValueLoci.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_value_nullity_degree]: the universal null-image
    property in the opening problem of 3.4.1, p. 310. Quantification retains
    every normed target, open source domain, and map of the given class.
    The measure has the original real degree and Gamma normalization.
    This is a definition of the problem, whose solution is due in 3.4.3. *)
Definition critical_value_nullity_degree (R:realType) (m nu k:nat)
    (s:R) (hs:0<=s):Prop:=
  forall (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (A:set (R_n R m)) (f:R_n R m->Y),
    (forall a,A a ->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) A a) ->
    norm_class (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY A f k ->
    @real_hausdorff_measure R (real_norm_metric_space hNY) s hs
      (critical_value_image NY A f nu)=0%E.

(** Source for [is_least_critical_value_degree]: the phrase "least number"
    in 3.4.1, p. 310, expressed within the nonnegative real degrees of
    2.10.2, p. 171. The two proof obligations are the upper theorem of
    3.4.3 and the sharpness examples of 3.4.4; neither is assumed here. *)
Record is_least_critical_value_degree (R:realType) (m nu k:nat)
    (s:R) (hs:0<=s):Prop:={
  (** Source for [critical_value_degree_attained]: the nullity assertion
      announced in 3.4.1, p. 310, to be proved by 3.4.3, pp. 316–317. *)
  critical_value_degree_attained:critical_value_nullity_degree m nu k hs;
  (** Source for [critical_value_degree_least]: the minimality assertion
      announced in 3.4.1, p. 310, to be proved by 3.4.4, pp. 317–318. *)
  critical_value_degree_least:forall (t:R) (ht:0<=t),
    critical_value_nullity_degree m nu k ht ->s<=t
}.
