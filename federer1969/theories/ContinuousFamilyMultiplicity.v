(** Supporting the affine double-slicing identities in Federer (1969),
    2.10.16, p. 178: joint counting measurability for an abstract continuous
    family, including singular linear maps. Use the incidence sets of
    ContinuousFamilyIncidence.v and the shrinking source partitions of
    2.10.10, p. 176. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ContinuousFamilyIncidence CompleteMetricUP SuslinSetUP SuslinMeasurability
  SuslinPartitionCostLimits ClosedCoverTreeUP CoverPartitionTreeUP ClosedCoverTreeSealed
  CoverPartitionTreeSealed PartitionHitCounts PartitionCountingLimit PartitionImageCharacteristicSum
  MappingMultiplicity CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureUP MeasureIntegralUP MeasurableFunctionUP MeasureExtendedCharacteristicIntegral
  TotalCountableNonnegativeIntegral NonnegativeSum NonnegativeSumSupport
  ExtendedRealOrderTopology ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum
  PartialFunctionBasic TotalExtendedLowerLimit ShrinkingBorelPartitionLevels.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [family_multiplicity]: supporting joint count
    N(e_p restricted to A,y) for 2.10.16, p. 178.
    The count is the existing actual counting measure of fibres. *)
Definition family_multiplicity (R : realType) (X Y P : choiceType)
    (e : P*X -> Y) (A : set X) (z : Y*P) : extended_real_line R :=
  @mapping_multiplicity R X Y (fun x => e (z.2,x)) A z.1.
Arguments family_multiplicity {R X Y P} e A z.

(** Source for [family_partition_characteristic_sum]: supporting
    partition count identity for 2.10.16, p. 178, extending
    the characteristic sum in 2.10.10, p. 176, to an
    abstract family. No measurability is needed for this identity. *)
Lemma family_partition_characteristic_sum (R : realType) (X Y P : choiceType)
    (e : P*X -> Y) (A : set X) (D : seq nat -> set X) j (z : Y*P) :
  nonnegative_sum [set s | size s=j]
    (fun s => (@CharacteristicFunction.value R (Y*P)%type (family_incidence e (A `&` D s)) z)%:E)=
    @partition_hit_count R X D (mapping_fibre (fun x => e (z.2,x)) A z.1) j.
Proof.
case: z=> y p.
have he : nonnegative_sum [set s | size s=j]
    (fun s => (@CharacteristicFunction.value R (Y*P)%type (family_incidence e (A `&` D s)) (y,p))%:E)=
    nonnegative_sum [set s | size s=j]
      (fun s => (@CharacteristicFunction.value R Y ((fun x => e (p,x)) @` (A `&` D s)) y)%:E).
  apply: nonnegative_sum_ext=> s hs.
  have hL := @CharacteristicFunction.laws R (Y*P)%type (family_incidence e (A `&` D s)).
  have hR := @CharacteristicFunction.laws R Y ((fun x => e (p,x)) @` (A `&` D s)).
  case: (pselect (((fun x => e (p,x)) @` (A `&` D s)) y))=> hy.
  - have hinc : family_incidence e (A `&` D s) (y,p).
      have [x hx he] := hy; exists x; split=> //; exact: esym he.
    by rewrite (characteristic_on_set hL hinc) (characteristic_on_set hR hy).
  - have hinc : ~family_incidence e (A `&` D s) (y,p).
      move=> [x [hx he]]; apply: hy; exists x=> //; exact: esym he.
    by rewrite (characteristic_off_set hL hinc) (characteristic_off_set hR hy).
rewrite he; exact: partition_image_characteristic_sum.
Qed.

(** Source for [continuous_family_multiplicity_measurable]: supporting
    actual joint measurability for the double-slicing argument
    in 2.10.16, p. 178. The source and parameter are
    complete separable metric spaces; the target is Hausdorff.
    The measure need only make closed sets measurable. Source
    nonemptiness is explicit infrastructure, discharged by R^n
    in the application, and the source set A may be empty. *)
Theorem continuous_family_multiplicity_measurable (R : realType)
    (X P : metricType R) (Y : topologicalType) (e : P*X -> Y)
    (mu : set (Y*P) -> \bar R) (hm : is_measure mu) (A : set X) :
  is_complete_metric_space X -> is_complete_metric_space P ->
  (exists D : set X, countable D /\ dense D) ->
  (exists D : set P, countable D /\ dense D) ->
  (@setT X)!=set0 -> hausdorff_space Y -> continuous e -> is_suslin_set R A ->
  (forall C, closed C -> measure_measurable mu C) ->
  is_measure_measurable_function mu (partial_function_total (family_multiplicity (R:=R) e A)).
Proof.
move=> hX hP hsX hsP hnon hY he hA hclosed.
have [B [hB hden]] := hsX.
pose E := @ClosedCoverTree.value R X B hB hden hnon.
pose D := @CoverPartitionTree.value X E.
have hE := @ClosedCoverTree.laws R X B hB hden hnon.
have hD := @CoverPartitionTree.laws X E.
pose F j (z : Y*P) : extended_real_line R :=
  @partition_hit_count R X D (mapping_fibre (fun x => e (z.2,x)) A z.1) j.
pose chi s := @CharacteristicFunction.value R (Y*P)%type (family_incidence e (A `&` D s)).
have hchi s := @CharacteristicFunction.laws R (Y*P)%type (family_incidence e (A `&` D s)).
have hinc s : measure_measurable mu (family_incidence e (A `&` D s)).
  apply: (@suslin_set_measurable R (Y*P)%type mu hm _ hclosed).
  exact (@continuous_family_incidence_suslin R X P Y e _ hX hP
    (ex_intro _ B (conj hB hden)) hsP hY he (@suslin_partition_cell R X E D hE hD A s hA)).
have hF j : is_measure_measurable_function mu (partial_function_total (F j)).
  have hi := @total_countable_nonnegative_integral R (Y*P)%type [the choiceType of (seq nat : Type)]
    mu hm [set s | size s=j] (fun s z => ((chi s z)%:E : extended_real_line R))
    (fun s => mu (family_incidence e (A `&` D s))) (@cover_partition_level_countable j)
    (fun s hs z => characteristic_extended_nonnegative (hchi s) z)
    (fun s hs => @measure_total_characteristic_integral R (Y*P)%type mu hm _ _ (hchi s) (hinc s)).
  have heq : (fun z => nonnegative_sum [set s | size s=j] (fun s => (chi s z)%:E))=F j.
    apply/funext=> z; exact: family_partition_characteristic_sum.
  by rewrite heq in hi; exact: hi.1.
have hlim z : extended_increases_to (fun j => F j z) (family_multiplicity (R:=R) e A z).
  exact: (@partition_hit_count_limit R X E D hE hD (mapping_fibre (fun x => e (z.2,x)) A z.1)).
have hmon i j z : (i<=j)%N -> F i z<=F j z := (hlim z).1 i j.
have heq : total_extended_lower_limit F=family_multiplicity (R:=R) e A.
  apply/funext=> z; exact: extended_order_limit_unique
    (total_extended_lower_limit_increases hmon z).2 (hlim z).2.
rewrite -heq; exact (@total_extended_lower_limit_measurable R (Y*P)%type mu hm F hF).
Qed.
