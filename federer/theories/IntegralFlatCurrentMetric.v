(** Federer (1969), 4.1.24, p. 382: the
    original integral flat quantity metrises the original
    additive integral-flat group. Use its opaque exact
    subgroup carrier, the independently specified infimum
    and the proved additive-size metric adapter. No real
    homogeneity or replacement vector space is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces AdditiveSubgroupRepresentationUP IntegralCurrentClassesUP
  IntegralCurrentGroupSpaces IntegralFlatSizeUP IntegralFlatSizeSealed
  IntegralFlatSizeComparison IntegralFlatSizeNegate IntegralFlatSizeTriangle AdditiveSizeMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section IntegralFlatCurrentMetric.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation G:=(@integral_flat_current_group R h2 n m U hU K).
Local Notation inc:=(@integral_flat_current_inclusion R h2 n m U hU K).
Local Notation hG:=(@integral_flat_current_group_laws R h2 n m U hU K).
Local Notation member:=(additive_subgroup_representation_member hG).
Local Notation Spec:=(@is_integral_flat_size R h2 n m U hU K).

(** Source for [integral_flat_current_size]: the original
    finite integral flat value on its opaque additive
    carrier, Federer 4.1.24, p. 382. *)
Definition integral_flat_current_size (z:G):R:=
  @IntegralFlatSize.value R h2 n m U hU K (inc z) (member z).

(** Source for [integral_flat_current_size_laws]: its value
    satisfies the independent original decomposition infimum
    laws on the actual included current, 4.1.24, p. 382. *)
Theorem integral_flat_current_size_laws z:Spec (inc z) (integral_flat_current_size z).
Proof. exact:IntegralFlatSize.laws. Qed.

(** Source for [integral_flat_current_size_is_additive_size]: the
    original nonnegative, even, definite and subadditive
    size on its abelian group, 4.1.24, p. 382. *)
Theorem integral_flat_current_size_is_additive_size:is_additive_size integral_flat_current_size.
Proof.
constructor.
- have h:=integral_flat_current_size_laws (0:G).
  rewrite raddf0 in h;exact:integral_flat_size_zero_current h.
- move=>z;exact:integral_flat_size_nonnegative (integral_flat_current_size_laws z).
- move=>z.
  have h:=integral_flat_current_size_laws (-z).
  rewrite raddfN in h.
  exact:(integral_flat_size_unique h
    (integral_flat_size_negate_specification (integral_flat_current_size_laws z))).
- move=>z w.
  have h:=integral_flat_current_size_laws (z+w).
  rewrite raddfD in h.
  exact:(integral_flat_size_triangle_specification
    (integral_flat_current_size_laws z) (integral_flat_current_size_laws w) h).
- move=>z hZero;apply:(additive_subgroup_representation_injective hG).
  rewrite raddf0.
  exact:(@integral_flat_size_definite R h2 n m U hU K (inc z)
    (integral_flat_current_size z) (member z) (integral_flat_current_size_laws z) hZero).
Qed.

(** Source for [integral_flat_current_metric]: the actual original
    additive carrier with distance given by integral flat
    size of its difference, Federer 4.1.24, p. 382. *)
Definition integral_flat_current_metric:metricType R:=
  [the metricType R of additive_size_metric_space integral_flat_current_size_is_additive_size].

(** Source for [integral_flat_current_distance_specification]: metric
    distance is the independent original infimum for the
    literal current difference, 4.1.24, p. 382. *)
Theorem integral_flat_current_distance_specification (z w:integral_flat_current_metric):
  Spec (inc z-inc w) (mdist z w).
Proof.
have h:=integral_flat_current_size_laws (z-w).
by rewrite raddfB in h.
Qed.

(** Source for [integral_flat_current_distance_value]: any original
    membership evidence for the difference gives the same
    distance value, Federer 4.1.24, p. 382. *)
Theorem integral_flat_current_distance_value (z w:integral_flat_current_metric)
    (hDifference:@is_integral_flat_current_supported_in R h2 n U hU m K (inc z-inc w)):
  mdist z w=@IntegralFlatSize.value R h2 n m U hU K (inc z-inc w) hDifference.
Proof.
exact:(integral_flat_size_unique (integral_flat_current_distance_specification z w)
  (@IntegralFlatSize.laws R h2 n m U hU K (inc z-inc w) hDifference)).
Qed.
End IntegralFlatCurrentMetric.
