(** Private existence witness for the scalar factor of Federer (1969),
    2.6.5, pp. 119–120, using the already proved Riemann-integral
    construction of 2.5.17, p. 111. Source context and comparison:
    LebesgueLineUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground LebesgueLineUP LebesgueLineCharacterisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_line_laws_exist]: existence of
    the measure characterised in Federer 2.5.17, p. 111,
    supplying the factor for 2.6.5, pp. 119–120. *)
Theorem lebesgue_line_laws_exist (R : realType) :
  exists mu : set R -> \bar R, is_lebesgue_line_measure mu.
Proof.
have [mu [hm [hr [_ [_ [_ [hs _]]]]]]] := @lebesgue_line_measure_characterisation R.
exists mu; by constructor.
Qed.
