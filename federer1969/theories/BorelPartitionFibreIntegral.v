(** Federer (1969), 3.2.11, p. 249: actual
    fibre measures sum over a subordinate Borel partition.
    This supporting form for 3.2.46, p. 282,
    first restricts the fibre measure by the whole
    original source, retaining arbitrary outer source sets. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import MappingMultiplicity BorelPartition FibreBorelPartitionMass
  MeasureUP MeasureBasic MeasureRestriction NonnegativeSum NonnegativeSumSupport
  PartialFunctionUP PartialFunctionBasic MeasureIntegralUP MeasureIntegralGraphEquivalence
  TotalCountableNonnegativeIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [mapping_fibre_borel_partition_mass]:
    exact fibre additivity in the proof of 3.2.11,
    p. 249, supporting 3.2.46, p. 282.
    Restrict sigma by the original S before using
    the Borel partition. In particular S itself and
    its individual fibres need not be sigma measurable. *)
Lemma mapping_fibre_borel_partition_mass (R : realType) (X : topologicalType)
    (Y : Type) (sigma : set X -> \bar R) (f : X -> Y) S H :
  is_measure sigma -> is_borel_partition setT H ->
  (forall B, H B -> measure_measurable sigma B) -> forall y,
  sigma (mapping_fibre f S y)=nonnegative_sum H
    (fun B=>sigma (mapping_fibre f (S `&` B) y)).
Proof.
move=> hSigma hH hMeas y.
have hSum := @borel_partition_fibre_mass_sum R X Y (measure_restrict sigma S)
  (measure_restrict_is_measure hSigma S) f setT H hH
  (fun B hB=>@measure_restrict_measurable R X sigma S B (hMeas B hB)) y.
have hRestriction T : measure_restrict sigma S (mapping_fibre f T y)=
    sigma (mapping_fibre f (S `&` T) y).
  congr (sigma _); apply/seteqP; split=> x.
  - move=> [hs [ht hxy]]; split; last exact hxy; by split.
  - move=> [[hs ht] hxy]; split; first exact hs; by split.
rewrite hRestriction setIT in hSum.
rewrite hSum; apply:nonnegative_sum_ext=> B hB; exact:hRestriction.
Qed.

(** Source for [borel_partition_fibre_integral]:
    integrate the exact original fibre sum in the
    extension of 3.2.11, p. 249, asserted by
    3.2.46, p. 282. Every local integral may
    be infinite and images of different source pieces
    may overlap; no finite mass or multiplicity is assumed. *)
Theorem borel_partition_fibre_integral (R : realType) (X : topologicalType)
    (Y : choiceType) (sigma : set X -> \bar R) (beta : set Y -> \bar R)
    (f : X -> Y) (S : set X) (H : set (set X)) (a : set X -> \bar R) :
  is_measure sigma -> is_measure beta -> is_borel_partition setT H ->
  (forall B, H B -> measure_measurable sigma B) ->
  (forall B, H B -> is_measure_integral beta (partial_function_total
    (fun y=>(sigma (mapping_fibre f (S `&` B) y) : extended_real_line R))) (a B)) ->
  is_measure_integral beta (partial_function_total
    (fun y=>(sigma (mapping_fibre f S y) : extended_real_line R))) (nonnegative_sum H a).
Proof.
move=> hSigma hBeta hH hMeas hLocal.
have hSum := @total_countable_nonnegative_integral R Y [the choiceType of set X] beta hBeta H
  (fun B y=>(sigma (mapping_fibre f (S `&` B) y) : extended_real_line R)) a
  (borel_partition_countable hH) (fun B hB y=>measure_nonnegative hSigma _) hLocal.
apply:(measure_integral_graph_equivalent _ hSum)=> y z.
change (nonnegative_sum H (fun B=>sigma (mapping_fibre f (S `&` B) y))=z <->
  sigma (mapping_fibre f S y)=z).
by rewrite -(@mapping_fibre_borel_partition_mass R X Y sigma f S H hSigma hH hMeas y).
Qed.
