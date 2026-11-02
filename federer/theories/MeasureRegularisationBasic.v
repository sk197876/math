(** Federer (1969), 2.1.5, p. 57: elementary consequences of the
    regularisation specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureRegularisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_regularisation_nonnegative]: Federer
    2.1.5, p. 57, supporting nonnegativity of the infimum of
    nonnegative measures of measurable supersets. *)
Lemma measure_regularisation_nonnegative (R : realType) (I : choiceType)
    (mu nu : set I -> \bar R) (hm : is_measure mu)
    (hr : is_measure_regularisation mu nu) A : 0 <= nu A.
Proof.
apply: (measure_regularisation_greatest hr)=> B _ _.
exact: (@measure_nonnegative R I mu hm).
Qed.

(** Source for [measure_regularisation_dominates]: Federer
    2.1.5, p. 57, supporting comparison of each set's measure
    with every measurable superset and hence with the regularisation. *)
Lemma measure_regularisation_dominates (R : realType) (I : choiceType)
    (mu nu : set I -> \bar R) (hm : is_measure mu)
    (hr : is_measure_regularisation mu nu) A : mu A <= nu A.
Proof.
apply: (measure_regularisation_greatest hr)=> B hAB _.
exact: (@measure_mono R I mu hm A B hAB).
Qed.

(** Source for [measure_regularisation_measurable_value]: Federer 2.1.5, p.
    57, final paragraph: the value is unchanged on every originally
    measurable set. *)
Lemma measure_regularisation_measurable_value (R : realType) (I : choiceType)
    (mu nu : set I -> \bar R) (hm : is_measure mu)
    (hr : is_measure_regularisation mu nu) A :
  measure_measurable mu A -> nu A = mu A.
Proof.
move=> hA; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@measure_regularisation_lower R I mu nu hr A A _ hA)=> x hx; exact hx.
- exact: (@measure_regularisation_dominates R I mu nu hm hr A).
Qed.

(** Source for [measure_regularisation_strict_approximation]: Federer 2.1.5,
    p. 57, supporting infimum approximation for the regularisation
    construction. *)
Lemma measure_regularisation_strict_approximation (R : realType) (I : choiceType)
    (mu nu : set I -> \bar R) (hr : is_measure_regularisation mu nu) A b :
  nu A < b -> exists B, A `<=` B /\ measure_measurable mu B /\ mu B < b.
Proof.
move=> hb; case: (pselect (exists B, A `<=` B /\ measure_measurable mu B /\ mu B < b))=> h; first exact h.
exfalso; have hbn : b <= nu A.
  apply: (measure_regularisation_greatest hr)=> B hAB hB.
  rewrite leNgt; apply/negP=> hlt; apply: h; exists B; by split=> //; split.
by move: hb; rewrite ltNge hbn.
Qed.
