(** Federer (1969), 3.2.11, p. 249: summing fibre
    masses over the subordinate Borel partition in the
    full-rank case. Use only measure restriction, 2.1.2,
    p. 54, and countable additivity, 2.1.3, p. 55. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import MappingMultiplicity BorelPartition MeasureUP MeasureRestriction
  NonnegativeSum NonnegativeSumSupport AreaInjectiveBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [mapping_fibre_restricted_mass]: the fibre
    mass in Federer 3.2.11, p. 249, is the value
    of the original measure restricted to the corresponding
    inverse point set. This supporting identity needs no
    continuity of f or measurability of its fibre. *)
Lemma mapping_fibre_restricted_mass (R:realType) (X:choiceType) (Y:Type)
    (beta:set X->\bar R) (f:X->Y) (A:set X) y:
  beta (mapping_fibre f A y)=measure_restrict beta [set x|f x=y] A.
Proof.
congr (beta _); apply/seteqP; split=>x [hx hy]; by split.
Qed.

(** Source for [borel_partition_fibre_mass_sum]: summing
    H^(m-n) fibre masses over H in Federer 3.2.11,
    p. 249. The supporting statement applies to any measure
    for which the Borel partition members are measurable, and
    includes empty partitions and infinite fibre masses. *)
Theorem borel_partition_fibre_mass_sum (R:realType) (X:topologicalType) (Y:Type)
    (beta:set X->\bar R) (hb:is_measure beta) (f:X->Y) A H:
  is_borel_partition A H ->(forall B,H B ->measure_measurable beta B) ->
  forall y,beta (mapping_fibre f A y)=nonnegative_sum H (fun B=>beta (mapping_fibre f B y)).
Proof.
move=>hH hMeas y.
rewrite mapping_fibre_restricted_mass.
have hMembers B:H B ->measure_measurable (measure_restrict beta [set x|f x=y]) B.
  move=>hB; exact (@measure_restrict_measurable R X beta [set x|f x=y] B (hMeas B hB)).
rewrite (measure_borel_partition_sum (measure_restrict_is_measure hb _) hH hMembers).
apply:nonnegative_sum_ext=>B hB; symmetry; exact:mapping_fibre_restricted_mass.
Qed.
