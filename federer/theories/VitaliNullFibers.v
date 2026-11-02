(** The exceptional set P in Federer (1969), 2.9.5, p. 154: points at which
    the subrelation of phi-null cells is fine form a phi-null set. This uses
    only the measure and Vitali laws, not existence of a derivate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import CoveringRelationUP MeasureUP MeasureBasic MeasureIndexedCover
  NonnegativeSum VitaliMassObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [vitali_null_fine_points_null]: the nullity
    of P in the proof of Federer 2.9.5,
    p. 154. A disjoint countable selection of
    null cells covers P almost everywhere; subadditivity
    suffices and no measurability of P is assumed. *)
Lemma vitali_null_fine_points_null (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure phi -> is_vitali_relation phi V ->
  phi [set x | covering_relation_fine_at (fun x S => V x S /\ phi S=0) x]=0.
Proof.
move=> hm hv.
pose C x S := V x S /\ phi S=0.
pose P := [set x | covering_relation_fine_at C x].
have hCV x S : C x S -> V x S by move=> [h _].
have hf x : P x -> covering_relation_fine_at C x by [].
have [G [hG [hcount [hdis hz]]]] := @vitali_relation_selection R X phi V hv C P hCV hf.
have hzero S : G S -> phi S=0.
  move=> hS; have [x [_ [_ h]]] := hG S hS; exact h.
have hcover := @null_remainder_measure_cover_bound R X phi P (\bigcup_(S in G) S) hm hz.
have hsum := @measure_indexed_cover R X [the choiceType of set X] phi hm
  (\bigcup_(S in G) S) G idfun hcount (fun _ h => h).
rewrite (nonnegative_sum_zero hzero) in hsum.
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
exact: le_trans hcover hsum.
Qed.
