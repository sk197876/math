(** Federer (1969), 3.3.4, p. 291: a nonempty
    pointwise supremum of outer measures is an outer measure.
    The assertion follows directly from countable covering
    and numerical-sum monotonicity, without regularity assumptions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBoundsUP MeasureFamilySupremumUP
  MeasureFamilySupremumSealed MeasureUP NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_family_supremum]: public value of
    the actual pointwise supremum used in the psi_v
    definition, Federer 3.3.4, p. 291. *)
Definition measure_family_supremum (R:realType) (X J:Type)
    (D:set J) (nu:J->set X->\bar R):=
  @MeasureFamilySupremum.value R X J D nu.

(** Source for [measure_family_supremum_specification]: the
    independent least-upper-bound laws for the public supremum,
    supporting Federer 3.3.4, p. 291. *)
Lemma measure_family_supremum_specification (R:realType) (X J:Type) D nu:
  is_measure_family_supremum D nu (@measure_family_supremum R X J D nu).
Proof. exact:MeasureFamilySupremum.laws. Qed.

(** Source for [measure_family_supremum_component]: each
    original weighted measure is dominated by psi_v,
    supporting Federer 3.3.4, p. 291. *)
Lemma measure_family_supremum_component (R:realType) (X J:Type)
    (D:set J) (nu:J->set X->\bar R) j A:
  D j ->nu j A<=measure_family_supremum D nu A.
Proof.
move=>hj; apply:(extended_real_supremum_upper
  (measure_family_supremum_specification D nu A)); by exists j.
Qed.

(** Source for [measure_family_supremum_is_measure]: the
    measure assertion for psi_v in Federer 3.3.4,
    p. 291. Any nonempty family of actual outer
    measures has an outer-measure supremum; there is no
    Borel regularity or finite-mass premise or conclusion. *)
Theorem measure_family_supremum_is_measure (R:realType) (X:choiceType) (J:Type)
    (D:set J) (nu:J->set X->\bar R):
  D!=set0 ->(forall j,D j ->is_measure (nu j)) ->
  is_measure (measure_family_supremum D nu).
Proof.
move=>[j0 hj0] hNu; constructor.
- move=>A; exact:(le_trans (measure_nonnegative (hNu j0 hj0) A)
    (measure_family_supremum_component nu A hj0)).
- move=>A F hF hCover.
  apply:(extended_real_supremum_least (measure_family_supremum_specification D nu A)).
  move=>z [j [hj ->]].
  apply:(le_trans (measure_countable_cover (hNu j hj) hF hCover)).
  apply:nonnegative_sum_mono=>B hB.
  exact:(measure_family_supremum_component nu B hj).
Qed.
