(** Federer (1969), 2.8.16, p. 151: covering relations, relation images,
    pointwise fineness and Vitali relations. The standing hypotheses on the
    measure are kept separate from these predicates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import CoveringFamilyUP TopologicalBorel ExtendedRealBounds MetricDiameter
  CountablyClosedFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_covering_relation]: direct definition in
    Federer 2.8.16, p. 151, first paragraph: every related
    pair (x,S) satisfies x in S. Relations are represented
    as predicates in two arguments rather than sets of pairs. *)
Definition is_covering_relation (X : Type) (C : X -> set X -> Prop) : Prop :=
  forall x S, C x S -> S x.

(** Source for [covering_relation_image]: direct formula C(Z) in Federer
    2.8.16, p. 151 It consists of sets related to some point of Z. *)
Definition covering_relation_image (X : Type) (C : X -> set X -> Prop) (Z : set X) :=
  [set S | exists x, Z x /\ C x S].

(** Source for [covering_relation_diameters]: the diameter set
    in the infimum defining fineness, Federer 2.8.16,
    p. 151. This supporting image uses the sealed diameter. *)
Definition covering_relation_diameters (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (x : X) :=
  [set d | exists S, C x S /\ d = extended_metric_diameter S].

(** Source for [covering_relation_fine_at]: direct zero-infimum definition
    of fineness at x in Federer 2.8.16, p. 151 Empty fibers are not fine. *)
Definition covering_relation_fine_at (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (x : X) : Prop :=
  extended_real_inf (covering_relation_diameters C x) = 0.

(** Source for [is_vitali_relation]: direct definition in Federer 2.8.16, p.
    151, second paragraph: a Borel covering relation fine everywhere whose
    fine subrelations admit countable disjointed almost-covering selections.
    Borel members need not be closed. *)
Record is_vitali_relation (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) : Prop := {
  (** Source for [vitali_relation_covering]: first defining
      clause of Federer 2.8.16, p. 151: V is covering. *)
  vitali_relation_covering : is_covering_relation V;
  (** Source for [vitali_relation_borel]: second defining
      clause of Federer 2.8.16, p. 151: V(X) is Borel. *)
  vitali_relation_borel : forall S, covering_relation_image V setT S -> borel_set S;
  (** Source for [vitali_relation_fine]: third defining clause
      of Federer 2.8.16, p. 151: fine at each point of X. *)
  vitali_relation_fine : forall x, covering_relation_fine_at V x;
  (** Source for [vitali_relation_selection]: the displayed conditional
    selection clause of Federer 2.8.16, p. 151 No measurability of Z or a
    testing-open-set condition is imposed here. *)
  vitali_relation_selection : forall (C : X -> set X -> Prop) (Z : set X),
    (forall x S, C x S -> V x S) ->
    (forall x, Z x -> covering_relation_fine_at C x) ->
    exists G : set (set X), G `<=` covering_relation_image C Z /\
      countable G /\ set_family_disjoint G /\
      phi (Z `\` \bigcup_(S in G) S) = 0
}.
