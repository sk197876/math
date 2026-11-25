(** Federer (1969), 2.2.5, p. 62, supporting Borel regularity and
    compact-set measurability from the Radon laws. Source context:
    RadonMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic TopologicalBorel BorelRegularMeasureUP
  BorelRegularisationUP BorelRegularisationAttainment RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_borel_regular]: supporting consequence of Federer
    2.2.5, p. 62, outer infimum over open supersets and open-set
    measurability. We use the previously proved attainment theorem for the
    intermediate Borel-superset infimum. *)
Lemma radon_borel_regular (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_radon_measure mu) : is_borel_regular_measure mu.
Proof.
have hs : is_borel_regularisation mu mu.
  constructor.
  - move=> A B hAB _; exact: (@measure_mono R _ mu hm A B hAB).
  - move=> A c hc; apply: (radon_outer_greatest hr)=> V hV hAV.
    exact: hc V hAV (open_borel_set hV).
constructor; first exact: radon_open_measurable hr.
move=> A; exact: (@borel_regularisation_attained R T mu mu hm hs A).
Qed.

(** Source for [radon_compact_measurable]: Federer 2.2.5, pp. 62-63,
    supporting compact-set measurability used in the approximation proof.
    Compact sets are closed in the Hausdorff ambient space. *)
Lemma radon_compact_measurable (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_radon_measure mu) K : compact K -> measure_measurable mu K.
Proof.
move=> hK; apply: (@borel_regular_borel_measurable R T mu hm (radon_borel_regular hm hr) K).
apply: closed_borel_set; exact: compact_closed (radon_hausdorff hr) hK.
Qed.
