(** Supporting finite coefficient recovery for Federer
    (1969), 3.2.45, p. 279.
    The existing basis and finite-dimensional inverse
    laws supply local witnesses only. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates BasisInterpolation EuclideanLinearMaps
  FinitePowerEvaluationUP FinitePowerEvaluationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_power_evaluation_inverse_exists]:
    supporting coefficient reconstruction from finitely many
    actual polynomial values in Federer 3.2.45,
    p. 279. Basis interpolation, 1.7.3,
    p. 30, gives the prescribed evaluation
    map. The proved original root count gives
    injectivity; the already proved finite-dimensional
    linear inverse gives both inverse laws.
    The maps remain local existential data.
    No globally selected inverse or extra polynomial
    library is introduced. *)
Theorem finite_power_evaluation_inverse_exists (R : realType) N :
  exists E G : {linear R_n R N.+1 -> R_n R N.+1},
    is_finite_power_evaluation E /\cancel E G /\cancel G E.
Proof.
pose v (i : 'I_N.+1) : R_n R N.+1 := [ffun j : 'I_N.+1 => ((j.+1)%:R)^+i].
pose E := basis_interpolation (@coordinate_basisP R N.+1) v.
have hE : is_finite_power_evaluation E.
  move=> c j; rewrite (@euclidean_linear_expansion R N.+1 E c) sum_ffunE.
  apply: eq_bigr=> i _.
  by rewrite /E basis_interpolationE /v !ffunE.
have [G [hLeft hRight]] := euclidean_linear_inverse (finite_power_evaluation_injective hE).
exists E,G; by split=> //; split.
Qed.
