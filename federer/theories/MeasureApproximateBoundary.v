(** Federer (1969), 3.2.16, p. 253:
    null-measure boundary of the approximation
    definition and the standing closure-domain
    convention in 3.1.22, p. 235. An
    empty actual graph gives a concrete boundary
    example for the unqualified relative assertion. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormDifferentialLocal NormOpenDomainLaws NormDifferentialLinear PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction MeasureUP NonnegativeSum MetricDensities
  MetricDensityZeroPowerMass TangentConeUP MeasureApproximateTangentUP
  MeasureApproximateDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_approximate_zero_measure_law]:
    the zero-measure boundary allowed by the
    arbitrary measure in Federer 3.2.16, p. 253.
    Its measure laws follow directly from 2.1.2. *)
Lemma measure_approximate_zero_measure_law (R : realType) (X : choiceType) :
  is_measure (fun _ : set X => (0 : \bar R)).
Proof.
constructor; first by move=> A; exact: lexx.
move=> A F _ _; exact: nonnegative_sum_nonnegative.
Qed.

(** Source for [measure_approximate_empty_zero]:
    a boundary of the definition in Federer
    3.2.16, p. 253: under zero measure
    even the empty function has a differentiable
    density-full representative. No value is inserted
    into its actual domain. *)
Theorem measure_approximate_empty_zero (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY) m (a : X) :
  measure_approximately_differentiable_at NY hNX (fun _=>0%E) m
    (@partial_function_empty X Y) a.
Proof.
exists (0 : Hom X Y); exists setT,(fun _ : X => (0 : Y)); split.
- exact: (@norm_differential_constant R X Y NX NY hNX hNY setT a 0
    (@norm_full_domain_interior R X NX a)).
- exact: (@null_set_metric_density_zero R (real_norm_metric_space hNX) m
    (fun _=>0%E) _ a (measure_approximate_zero_measure_law R X) erefl).
Qed.

(** Source for [measure_approximate_empty_agreement_not_closure]:
    the closure-domain qualification inherited from
    Federer 3.1.22, p. 235, in the
    relative assertion of 3.2.16, p. 253.
    An empty actual graph has empty agreement
    with every representative, so no base point
    belongs to that agreement's closure. *)
Lemma measure_approximate_empty_agreement_not_closure (R : realType)
    (X Y : lmodType R) (NX : X -> R) (hNX : is_real_norm NX)
    (U : set X) (g : X -> Y) (a : X) :
  ~@closure (real_norm_metric_space hNX)
    (partial_function_agreement (@partial_function_empty X Y)
      (partial_function_source_restrict U (partial_function_total g))) a.
Proof.
have he : partial_function_agreement (@partial_function_empty X Y)
    (partial_function_source_restrict U (partial_function_total g))=set0.
  apply/seteqP; split=> x; [by move=> [y [[] _]]|by move=> []].
by rewrite he closure0.
Qed.

(** Source for [measure_approximate_zero_tangent_empty]:
    the empty-cone boundary permitted by the
    intersection definition of Federer 3.2.16,
    p. 252. Under zero measure the empty
    set is density-full and its tangent cone
    is empty, so the intersection is empty. *)
Lemma measure_approximate_zero_tangent_empty (R : realType) (X : lmodType R)
    (NX : X -> R) (hNX : is_real_norm NX) m (a : X) :
  measure_approximate_tangent_cone hNX (fun _=>0%E) m a=set0.
Proof.
apply/seteqP; split=> v; last by move=> [].
move=> hv.
have hZero := @null_set_metric_density_zero R (real_norm_metric_space hNX) m
  (fun _=>0%E) (~` set0) a (measure_approximate_zero_measure_law R X) erefl.
have [x [r [[] _]]] := hv set0 hZero 1 (@ltr01 R).
Qed.
