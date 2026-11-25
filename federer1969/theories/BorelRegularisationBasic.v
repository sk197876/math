(** Federer (1969), 2.2.3, p. 62, final paragraph: regularisation by the
    infimum over Borel supersets. The construction is sealed; mathematical
    consequences use its greatest-lower-bound laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import TopologicalBorel MeasureUP MeasureBasic BorelRegularisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_regularisation_nonnegative]: Federer
    2.2.3, p. 62, supporting nonnegativity of the infimum of
    nonnegative measures of Borel supersets. *)
Lemma borel_regularisation_nonnegative (R : realType) (I : topologicalType)
    (mu nu : set I -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regularisation mu nu) A : 0 <= nu A.
Proof.
apply: (borel_regularisation_greatest hr)=> B _ _.
exact: (@measure_nonnegative R I mu hm).
Qed.

(** Source for [borel_regularisation_dominates]: Federer
    2.2.3, p. 62, supporting comparison of each set's measure
    with every Borel superset and hence with the regularisation. *)
Lemma borel_regularisation_dominates (R : realType) (I : topologicalType)
    (mu nu : set I -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regularisation mu nu) A : mu A <= nu A.
Proof.
apply: (borel_regularisation_greatest hr)=> B hAB _.
exact: (@measure_mono R I mu hm A B hAB).
Qed.

(** Source for [borel_regularisation_borel_value]: Federer 2.2.3, p. 62,
    final paragraph: the value is unchanged on every Borel set. *)
Lemma borel_regularisation_borel_value (R : realType) (I : topologicalType)
    (mu nu : set I -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regularisation mu nu) A :
  borel_set A -> nu A = mu A.
Proof.
move=> hA; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@borel_regularisation_lower R I mu nu hr A A _ hA)=> x hx; exact hx.
- exact: (@borel_regularisation_dominates R I mu nu hm hr A).
Qed.

(** Source for [borel_regularisation_strict_approximation]: Federer 2.2.3,
    p. 62, supporting approximation of the displayed infimum by Borel
    supersets. *)
Lemma borel_regularisation_strict_approximation (R : realType) (I : topologicalType)
    (mu nu : set I -> \bar R) (hr : is_borel_regularisation mu nu) A b :
  nu A < b -> exists B, A `<=` B /\ borel_set B /\ mu B < b.
Proof.
move=> hb; case: (pselect (exists B, A `<=` B /\ borel_set B /\ mu B < b))=> h; first exact h.
exfalso; have hbn : b <= nu A.
  apply: (borel_regularisation_greatest hr)=> B hAB hB.
  rewrite leNgt; apply/negP=> hlt; apply: h; exists B; by split=> //; split.
by move: hb; rewrite ltNge hbn.
Qed.
