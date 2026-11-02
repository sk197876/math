(** Federer (1969), 2.8.1, pp. 141–142: standing metric measure hypotheses,
    fine coverings and adequate families. the context below retains
    Federer's hypotheses. All specifications below are predicates, not
    project axioms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP CountablyClosedFamilyUP
  MetricClosedBalls MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_open_ball]: direct definition of U(a,r)
    in Federer 2.8.1, p. 141: points at distance strictly less
    than r from a. The standing discussion uses positive radii;
    this set expression also makes sense for other real radii.
    The companion B(a,r) is the existing metric_closed_ball. *)
Definition metric_open_ball (R : realType) (X : metricType R)
    (a : X) (r : R) : set X := [set x | (mdist a x < r)%R].

(** Source for [metric_set_bounded]: boundedness in the standing
    hypotheses of Federer 2.8.1, p. 141, expressed by finiteness
    of the previously specified extended diameter. Empty sets have
    diameter zero. No compactness or separability is imposed. *)
Definition metric_set_bounded (R : realType) (X : metricType R)
    (A : set X) := extended_metric_diameter A < +oo.

(** Source for [is_covering_theory_context]: the standing hypotheses of
    Federer 2.8.1, p. 141. F consists of closed sets, open sets are
    measurable, and bounded sets have finite measure. These hypotheses are
    separate from the definitions of fineness and adequacy, so later results
    can state precisely which parts they use. *)
Record is_covering_theory_context (R : realType) (X : metricType R)
    (F : set (set X)) (mu : set X -> \bar R) : Prop := {
  (** Source for [covering_context_measure]: "phi measures X"
      in Federer 2.8.1, p. 141, with measure understood as in
      2.1.2, p. 53, on all subsets. *)
  covering_context_measure : is_measure mu;
  (** Source for [covering_context_closed]: F is a family of
      closed subsets, Federer 2.8.1, p. 141. Empty members
      are permitted here; the additional nonemptiness condition
      in the corrected 2.8.4 is a separate hypothesis. *)
  covering_context_closed : forall B, F B -> closed B;
  (** Source for [covering_context_open_measurable]: every open
      subset is measurable, Federer 2.8.1, p. 141. *)
  covering_context_open_measurable : forall V, open V -> measure_measurable mu V;
  (** Source for [covering_context_bounded_finite]: every bounded
      subset has finite measure, Federer 2.8.1, p. 141.
      This does not assert Borel regularity. *)
  covering_context_bounded_finite : forall A, metric_set_bounded A -> mu A < +oo
}.

(** Source for [family_covers_finely]: direct definition in Federer 2.8.1,
    p. 142, first paragraph: for each a in A and each positive epsilon, some
    B in F contains a and lies in U(a,epsilon). *)
Definition family_covers_finely (R : realType) (X : metricType R)
    (F : set (set X)) (A : set X) : Prop :=
  forall a, A a -> forall epsilon : R, (0 < epsilon)%R ->
    exists B, F B /\ B a /\ B `<=` metric_open_ball a epsilon.

(** Source for [is_adequate_cover_selection]: the countable
    disjointed subfamily G required for an open V by Federer
    2.8.1, p. 142, second paragraph and display. This record
    specifies a witness by its laws; it does not select one. *)
Record is_adequate_cover_selection (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (F : set (set X)) (A V : set X)
    (G : set (set X)) : Prop := {
  (** Source for [adequate_selection_members]: G is a subfamily
      of F, Federer 2.8.1, p. 142. *)
  adequate_selection_members : G `<=` F;
  (** Source for [adequate_selection_countable]: G is countable,
      Federer 2.8.1, p. 142. *)
  adequate_selection_countable : countable G;
  (** Source for [adequate_selection_disjoint]: G is disjointed,
      Federer 2.8.1, p. 142; distinct sets have empty intersection. *)
  adequate_selection_disjoint : set_family_disjoint G;
  (** Source for [adequate_selection_within]: union G is contained
      in V, Federer 2.8.1, p. 142, first condition of the display. *)
  adequate_selection_within : (\bigcup_(B in G) B) `<=` V;
  (** Source for [adequate_selection_remainder]: the remainder
      (V intersect A) minus union G is null, Federer 2.8.1,
      p. 142, second condition of the display. *)
  adequate_selection_remainder : mu ((V `&` A) `\` \bigcup_(B in G) B) = 0
}.

(** Source for [family_is_measure_adequate]: direct definition of "F is phi
    adequate for A" in Federer 2.8.1, p. 142. The target A need not itself
    be measurable or bounded. *)
Definition family_is_measure_adequate (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (F : set (set X)) (A : set X) : Prop :=
  forall V, open V -> exists G, is_adequate_cover_selection mu F A V G.
