(** Supporting affine and rotational parameter substitutions in Federer
    (1969), 2.10.16, p. 178. Continuous preimages of the family's Suslin
    incidence sets are measurable for any source measure making closed sets
    measurable. This retains the stronger property needed before composing a
    completed-measurable counting function. It uses 2.2.10, pp. 65–66,
    2.2.12, p. 68, and the partition limit in 2.10.10, p. 176. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ContinuousFamilyIncidence ContinuousFamilyMultiplicity CompleteMetricUP
  SuslinSetUP SuslinPreimages SuslinMeasurability SuslinPartitionCostLimits
  ClosedCoverTreeUP CoverPartitionTreeUP ClosedCoverTreeSealed CoverPartitionTreeSealed
  PartitionHitCounts PartitionCountingLimit MappingMultiplicity
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureExtendedCharacteristicIntegral
  TotalCountableNonnegativeIntegral NonnegativeSum NonnegativeSumSupport
  ExtendedRealOrderTopology ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum
  PartialFunctionBasic TotalExtendedLowerLimit ShrinkingBorelPartitionLevels
  MeasureUP MeasureIntegralUP MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_family_multiplicity_precomposition_measurable]:
    supporting actual measurability after the affine parameter
    substitutions in 2.10.16, p. 178. The parameter
    family is defined on a complete separable metric space;
    the new source T is arbitrary topological and no
    sigma-finiteness assumption on its measure is added. *)
Theorem continuous_family_multiplicity_precomposition_measurable (R : realType)
    (X P : metricType R) (Y T : topologicalType) (e : P*X -> Y)
    (mu : set T -> \bar R) (hm : is_measure mu) (u : T -> Y*P) (A : set X) :
  is_complete_metric_space X -> is_complete_metric_space P ->
  (exists D : set X, countable D /\ dense D) ->
  (exists D : set P, countable D /\ dense D) ->
  (@setT X)!=set0 -> hausdorff_space Y -> continuous e -> continuous u ->
  is_suslin_set R A -> (forall C, closed C -> measure_measurable mu C) ->
  is_measure_measurable_function mu
    (partial_function_total (fun t => family_multiplicity (R:=R) e A (u t))).
Proof.
move=> hX hP hsX hsP hnon hY he hu hA hclosed.
have [B [hB hden]] := hsX.
pose E := @ClosedCoverTree.value R X B hB hden hnon.
pose D := @CoverPartitionTree.value X E.
have hE := @ClosedCoverTree.laws R X B hB hden hnon.
have hD := @CoverPartitionTree.laws X E.
pose F j t : extended_real_line R :=
  @partition_hit_count R X D (mapping_fibre (fun x => e ((u t).2,x)) A (u t).1) j.
pose chi s := @CharacteristicFunction.value R (Y*P)%type (family_incidence e (A `&` D s)).
have hchi s : is_characteristic_function (u @^-1` family_incidence e (A `&` D s))
    (fun t => chi s (u t)).
  have hh := @CharacteristicFunction.laws R (Y*P)%type (family_incidence e (A `&` D s)).
  constructor; [move=> t ht; exact (characteristic_on_set hh ht)|
    move=> t ht; exact (characteristic_off_set hh ht)].
have hinc s : measure_measurable mu (u @^-1` family_incidence e (A `&` D s)).
  apply: (@suslin_set_measurable R T mu hm _ hclosed).
  apply: (@continuous_preimage_suslin R T (Y*P)%type u _ hu).
  exact (@continuous_family_incidence_suslin R X P Y e _ hX hP
    (ex_intro _ B (conj hB hden)) hsP hY he (@suslin_partition_cell R X E D hE hD A s hA)).
have hF j : is_measure_measurable_function mu (partial_function_total (F j)).
  have hi := @total_countable_nonnegative_integral R T [the choiceType of (seq nat : Type)]
    mu hm [set s | size s=j] (fun s t => ((chi s (u t))%:E : extended_real_line R))
    (fun s => mu (u @^-1` family_incidence e (A `&` D s))) (@cover_partition_level_countable j)
    (fun s hs t => characteristic_extended_nonnegative (hchi s) t)
    (fun s hs => @measure_total_characteristic_integral R T mu hm _ _ (hchi s) (hinc s)).
  have heq : (fun t => nonnegative_sum [set s | size s=j] (fun s => (chi s (u t))%:E))=F j.
    apply/funext=> t; exact: family_partition_characteristic_sum.
  by rewrite heq in hi; exact: hi.1.
have hlim t : extended_increases_to (fun j => F j t) (family_multiplicity (R:=R) e A (u t)).
  exact: (@partition_hit_count_limit R X E D hE hD (mapping_fibre (fun x => e ((u t).2,x)) A (u t).1)).
have hmon i j t : (i<=j)%N -> F i t<=F j t := (hlim t).1 i j.
have heq : total_extended_lower_limit F=(fun t => family_multiplicity (R:=R) e A (u t)).
  apply/funext=> t; exact: extended_order_limit_unique
    (total_extended_lower_limit_increases hmon t).2 (hlim t).2.
rewrite -heq; exact (@total_extended_lower_limit_measurable R T mu hm F hF).
Qed.
