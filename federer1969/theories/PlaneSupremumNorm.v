(** Public coordinate-supremum norm mu for Federer (1969), 2.10.44, printed
    p. 202. The evaluation and real norm laws are derived solely from the
    opaque order specification. Source context: PlaneSupremumNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations RealNormUP NormMetric
  PlaneSupremumNormUP PlaneSupremumNormLaws PlaneSupremumNormSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [plane_supremum_norm]: abstract norm
    mu in the printed counterexample of 2.10.44,
    p. 202. No maximum implementation is exposed. *)
Definition plane_supremum_norm (R : realType) : R_n R 2 -> R := @PlaneSupremumNorm.value R.

(** Source for [plane_supremum_norm_specification]: proved
    least-coordinate-bound laws for mu in 2.10.44,
    p. 202. *)
Lemma plane_supremum_norm_specification (R : realType) : is_plane_supremum_norm (@plane_supremum_norm R).
Proof. exact: PlaneSupremumNorm.laws. Qed.

(** Source for [plane_supremum_normE]: direct printed
    formula mu(x)=max(|x_1|,|x_2|) in 2.10.44,
    p. 202, derived from the abstract supremum laws. *)
Lemma plane_supremum_normE (R : realType) (x : R_n R 2) :
  plane_supremum_norm x=Num.max `|x ord0| `|x ord_max|.
Proof. exact (@plane_supremum_norm_value R (@plane_supremum_norm R) (@plane_supremum_norm_specification R) x). Qed.

(** Source for [plane_supremum_normP]: supporting
    real norm assertion for mu in 2.10.44,
    p. 202, proved from the abstract specification. *)
Lemma plane_supremum_normP (R : realType) : is_real_norm (@plane_supremum_norm R).
Proof. exact (@plane_supremum_norm_is_real_norm R (@plane_supremum_norm R) (@plane_supremum_norm_specification R)). Qed.

(** Source for [plane_supremum_metric]: supporting
    remetrised source R^2 in 2.10.44, p. 202.
    Its metric is the one induced by the proved
    real norm mu, through the existing norm-metric interface. *)
Definition plane_supremum_metric (R : realType) := real_norm_metric_space (plane_supremum_normP R).
