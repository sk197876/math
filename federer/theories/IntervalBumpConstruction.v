(** Federer (1969), 3.2.33, p. 270: all scalar
    data of the printed smooth counterexample exist together. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import PositiveUnitIntervalBumpUP PositiveUnitIntervalBumpExistence
  DenseSmallIntervalFamilyUP DenseSmallIntervalFamilyExistence IntervalBumpSeriesUP IntervalBumpSeriesExistence
  IntervalBumpPrimitiveUP IntervalBumpPrimitiveExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [interval_bump_construction_exists]: the actual
    choices phi, U_j, psi and g in Federer 3.2.33,
    p. 270. Each independent specification is discharged by
    a proved existence theorem; no existence, convergence,
    differentiability, injectivity or omitted positive measure
    hypothesis is left for the final example to assume. *)
Theorem interval_bump_construction_exists (R:realType):
  exists (a b:nat->R) (phi psi g:R->R),
    is_positive_unit_interval_bump phi /\is_dense_small_interval_family a b /\
    is_interval_bump_series a b phi psi /\is_interval_bump_primitive a b psi g.
Proof.
have [phi hPhi]:=positive_unit_interval_bump_exists R.
have [a [b hFamily]]:=dense_small_interval_family_exists R.
have [psi hSeries]:=interval_bump_series_exists hPhi hFamily.
have [g hG]:=interval_bump_primitive_exists hFamily hSeries.
exists a,b,phi,psi,g; exact:(conj hPhi (conj hFamily (conj hSeries hG))).
Qed.
