(** Federer (1969), 4.1.8, p. 361: the original
    product measure on the naturally identified Euclidean
    product domain. Specify precisely the original product
    under the existing block bijection. Construction serves
    only existence; the public condition fixes every set value. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanCartesianMap CurrentDomain
  CurrentCartesianDomainMapsSealed CurrentCartesianDomainMapsLaws
  MeasureUP ProductMeasure MeasurePushforward MeasureBijectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section CurrentCartesianMeasureUP.
Variable R:realType.
Variables m n:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Local Notation AT := (current_domain R m A).
Local Notation BT := (current_domain R n B).
Local Notation CT := (current_domain R (m+n) (@euclidean_cartesian_set R m n A B)).
Local Notation J := (@CartesianCurrentDomain.join R m n A B).
Local Notation D := (@CartesianCurrentDomain.split R m n A B).
Variables (alpha:set AT->\bar R) (beta:set BT->\bar R).
Hypothesis hAlpha:is_measure alpha.
Hypothesis hBeta:is_measure beta.

(** Source for [is_current_cartesian_measure]: the original
    product measure through its natural original coordinate
    bijection, supporting Federer 4.1.8, p. 361,
    by 2.6.5, p. 120. All set values are
    fixed; no Radon or representation conclusion is assumed. *)
Definition is_current_cartesian_measure (lambda:set CT->\bar R):Prop:=
  is_measure lambda /\is_measure_bijection (product_measure hAlpha hBeta) lambda J D.

(** Source for [current_cartesian_measure_exists]: the original
    product has an actual measure on the original
    product domain, supporting Federer 4.1.8, p. 361.
    Its image construction proves existence only. *)
Theorem current_cartesian_measure_exists:
  exists lambda:set CT->\bar R,is_current_cartesian_measure lambda.
Proof.
pose lambda:=measure_pushforward J (product_measure hAlpha hBeta).
exists lambda;split;first exact:measure_pushforward_is_measure (product_measure_is_measure hAlpha hBeta).
constructor.
- exact:current_cartesian_domain_join_split.
- exact:current_cartesian_domain_split_join.
- reflexivity.
Qed.

(** Source for [current_cartesian_measure_unique]: the original
    product set values uniquely determine this measure,
    supporting Federer 4.1.8, p. 361. *)
Theorem current_cartesian_measure_unique (lambda mu:set CT->\bar R):
  is_current_cartesian_measure lambda->is_current_cartesian_measure mu->lambda=mu.
Proof.
move=>hLambda hMu.
exact:(eq_trans (esym (measure_bijection_pushforward hLambda.2))
  (measure_bijection_pushforward hMu.2)).
Qed.
End CurrentCartesianMeasureUP.
