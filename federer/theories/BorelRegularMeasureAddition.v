(** Supporting Borel hulls for the derivative variation measure in Federer
    (1969), 2.9.22, p. 168, using the sum of continuous parts from 2.9.19,
    p. 165. Finite sums of Borel regular measures remain Borel regular by
    intersecting their Borel hulls; this is a consequence of 2.2.3, p. 61,
    not an additional measure axiom. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel BorelFamilyBasic
  MeasureBinaryAddition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_binary_addition_borel_regular]: supporting
    Borel hull for the zero weighted derivative integral in Federer
    2.9.22, p. 168. Intersect a hull for each summand; monotonicity
    makes both masses exact on their common hull, even if infinite. *)
Lemma measure_binary_addition_borel_regular (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) : is_measure mu -> is_measure nu ->
  is_borel_regular_measure mu -> is_borel_regular_measure nu ->
  is_borel_regular_measure (fun A => mu A+nu A).
Proof.
move=> hm hn hr hs; constructor.
- move=> U hU; apply: measure_binary_addition_measurable;
    [exact: (@borel_regular_open_measurable R X mu hr U hU)|exact: (@borel_regular_open_measurable R X nu hs U hU)].
- move=> A.
  have [B [hAB [hB hmu]]] := borel_regular_cover hr A.
  have [C [hAC [hC hnu]]] := borel_regular_cover hs A.
  have hAI : A `<=` B `&` C by move=> x hx; split; [exact: hAB|exact: hAC].
  exists (B `&` C); split=> //; split; first exact (@borel_family_binary_intersection _ setT _ (borel_sets_family X) B C hB hC).
  have heM : mu A=mu (B `&` C).
    apply: le_anti; apply/andP; split; first exact: (@measure_mono R X mu hm _ _ hAI).
    rewrite hmu; apply: (@measure_mono R X mu hm)=> x [hx _]; exact hx.
  have heN : nu A=nu (B `&` C).
    apply: le_anti; apply/andP; split; first exact: (@measure_mono R X nu hn _ _ hAI).
    rewrite hnu; apply: (@measure_mono R X nu hn)=> x [_ hx]; exact hx.
  by rewrite heM heN.
Qed.
