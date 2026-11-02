(** Federer (1969), 2.5.17, p. 111, the characterisation of L^1 by Borel
    regularity and segment length, used as the scalar factor in 2.6.5, pp.
    119–120. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MeasureUP BorelRegularMeasureUP LebesgueLineCharacterisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_lebesgue_line_measure]: abstract laws of
    L^1 in Federer 2.5.17, p. 111, used for 2.6.5,
    pp. 119–120. Existence is a separate proved result. *)
Record is_lebesgue_line_measure (R : realType) (mu : set R -> \bar R) : Prop := {
  (** Source for [lebesgue_line_measure_law]: measure law in
      Federer 2.5.17, p. 111. *)
  lebesgue_line_measure_law : is_measure mu;
  (** Source for [lebesgue_line_borel_law]: Borel regularity
      in Federer 2.5.17, p. 111. *)
  lebesgue_line_borel_law : is_borel_regular_measure mu;
  (** Source for [lebesgue_line_segment_law]: segment length
      in Federer 2.5.17, p. 111; the already proved
      degenerate case a=b is included. *)
  lebesgue_line_segment_law : forall a b, a <= b -> mu `[a,b] = (b-a)%:E
}.

(** Source for [lebesgue_line_unique]: the uniqueness in
    the characterisation of Federer 2.5.17, p. 111,
    ensuring that finite products in 2.6.5 are intrinsic. *)
Theorem lebesgue_line_unique (R : realType) (mu nu : set R -> \bar R) :
  is_lebesgue_line_measure mu -> is_lebesgue_line_measure nu -> mu = nu.
Proof.
move=> [hm hr hs] [hn hnr hns].
exact: borel_regular_interval_unique hm hn hr hnr hs hns.
Qed.
