(** Federer (1969), 4.1.24, p. 382: metrize
    the actual opaque rectifiable additive group by the
    original mass of its current difference. All masses
    are finite by the original approximation property.
    Use an additive size, without asserting real scalar
    closure of the integer rectifiable class. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentMassSealed CurrentMassBasic CurrentMassFiniteAlgebra
  CurrentFiniteMassNegation CurrentFiniteMassTriangle CurrentMassZeroDetection
  AdditiveSubgroupRepresentationUP RectifiableCurrentApproximationUP RectifiableCurrentBasic
  IntegralCurrentGroupSpaces AdditiveSizeMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section RectifiableCurrentMassMetric.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation G:=(@rectifiable_current_group R h2 n m U hU K).
Local Notation inc:=(@rectifiable_current_inclusion R h2 n m U hU K).
Local Notation hG:=(@rectifiable_current_group_laws R h2 n m U hU K).
Local Notation member:=(additive_subgroup_representation_member hG).
Local Notation M:=(@CurrentMass.value R h2 n m U hU).

(** Source for [rectifiable_current_mass_size]: the finite
    original mass on its actual opaque rectifiable
    additive carrier, Federer 4.1.24, p. 382. *)
Definition rectifiable_current_mass_size (z:G):R:=fine (M (inc z)).

(** Source for [rectifiable_current_mass_value]: the mass-size
    abbreviation retains exactly the original current mass,
    Federer 4.1.24, p. 382. *)
Theorem rectifiable_current_mass_value z:
  M (inc z)=(rectifiable_current_mass_size z)%:E.
Proof.
have hFinite:=@rectifiable_current_finite_mass R h2 n m U hU K (inc z) (member z).
have hNumber:M (inc z) \is a fin_num.
  rewrite (ge0_fin_numE (@current_mass_nonnegative R h2 n m U hU (inc z))).
  exact:hFinite.
by rewrite /rectifiable_current_mass_size fineK.
Qed.

(** Source for [rectifiable_current_mass_size_laws]: the original
    mass is a nonnegative even definite subadditive size
    on the rectifiable additive group, 4.1.24, p. 382. *)
Theorem rectifiable_current_mass_size_laws:is_additive_size rectifiable_current_mass_size.
Proof.
constructor.
- by rewrite /rectifiable_current_mass_size raddf0 current_mass_zero fine0.
- move=>z;have h:=@current_mass_nonnegative R h2 n m U hU (inc z).
  by rewrite (rectifiable_current_mass_value z) lee_fin in h.
- move=>z.
  have hMass:=@current_finite_mass_negation R h2 n m U hU (inc z)
    (@rectifiable_current_finite_mass R h2 n m U hU K (inc z) (member z)).
  have hNegValue:=rectifiable_current_mass_value (-z).
  rewrite raddfN in hNegValue.
  have hValues:=eq_trans (esym hNegValue) (eq_trans hMass (rectifiable_current_mass_value z)).
  exact:EFin_inj hValues.
- move=>z w.
  have hTriangle:=@current_finite_mass_triangle R h2 n m U hU (inc z) (inc w)
    (@rectifiable_current_finite_mass R h2 n m U hU K (inc z) (member z))
    (@rectifiable_current_finite_mass R h2 n m U hU K (inc w) (member w)).
  have hSumValue:=rectifiable_current_mass_value (z+w).
  rewrite raddfD in hSumValue.
  by rewrite hSumValue (rectifiable_current_mass_value z)
    (rectifiable_current_mass_value w) -EFinD lee_fin in hTriangle.
- move=>z hZero;apply:(additive_subgroup_representation_injective hG).
  rewrite raddf0;apply:(@current_mass_zero_implies_zero R h2 n m U hU).
  by rewrite (rectifiable_current_mass_value z) hZero.
Qed.

(** Source for [rectifiable_current_mass_metric]: the actual
    original rectifiable group with its mass-distance topology,
    Federer 4.1.24, p. 382. *)
Definition rectifiable_current_mass_metric:metricType R:=
  [the metricType R of additive_size_metric_space rectifiable_current_mass_size_laws].

(** Source for [rectifiable_current_mass_distance_value]: distance
    is exactly M(T-S), with the original actual included
    currents, Federer 4.1.24, p. 382. *)
Theorem rectifiable_current_mass_distance_value (z w:rectifiable_current_mass_metric):
  M (inc z-inc w)=(mdist z w)%:E.
Proof.
have h:=rectifiable_current_mass_value (z-w).
by rewrite raddfB in h.
Qed.
End RectifiableCurrentMassMetric.
