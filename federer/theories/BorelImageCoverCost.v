(** Federer (1969), 2.10.10, p. 176: the cost zeta(S)=beta(f[S]) satisfies
    the covering inequality of 2.10.8, p. 175. This follows directly from
    the measure covering law; image measurability is needed later for the
    integral identity, not for this inequality. Source context and relation
    to 2.5.10: BorelCoverCostUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureIndexedCover BorelCoverCostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_image_cover_cost]: the displayed
    image cost in Federer 2.10.10, p. 176.
    It is defined on every set; the Borel-cover construction
    restricts its use to Borel generators. *)
Definition borel_image_cover_cost (X Y : Type) (R : realType)
    (f : X -> Y) (beta : set Y -> \bar R) (A : set X) := beta (f @` A).

(** Source for [borel_image_cover_cost_laws]: the
    applicability of 2.10.8, p. 175, to the
    cost in Federer 2.10.10, p. 176.
    No continuity or injectivity is needed for this
    supporting covering inequality. *)
Lemma borel_image_cover_cost_laws (R : realType) (X : topologicalType)
    (Y : choiceType) (f : X -> Y) (beta : set Y -> \bar R) :
  is_measure beta -> is_borel_cover_cost (borel_image_cover_cost f beta).
Proof.
move=> hb; constructor.
- move=> A hA; exact: (@measure_nonnegative R Y beta hb (f @` A)).
- move=> J D S A hD hA hS hcover.
  apply: (@measure_indexed_cover R Y J beta hb (f @` A) D (fun j => f @` S j) hD).
  move=> y [x hx <-]; have [j hj hxj] := hcover x hx.
  exists j=> //; by exists x.
Qed.
