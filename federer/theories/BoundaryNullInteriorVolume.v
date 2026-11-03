(** Federer (1969), 3.2.43, printed p. 278:
    once actual ambient boundary volume is zero, the
    original interior and closure have equal volumes. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes TopologicalBorel MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [boundary_null_interior_closure_volume]: supporting
    use of the last observation in the proof of Federer
    3.2.43, p. 278. Actual Caratheodory splitting by Int S
    proves equal closure and interior volumes. No measurability
    of S or finite-volume hypothesis is needed for this identity. *)
Lemma boundary_null_interior_closure_volume (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  @euclidean_lebesgue_measure R n (closure S `\` interior S)=0%E ->
  @euclidean_lebesgue_measure R n (closure S)=
    @euclidean_lebesgue_measure R n (interior S).
Proof.
move=>hNull.
have hMeas:measure_measurable (@euclidean_lebesgue_measure R n) (interior S).
  apply:euclidean_borel_measurable; exact:open_borel_set (open_interior S).
have hIntersection:closure S `&` interior S=interior S.
  apply/seteqP; split=>[x [_ hx]//|x hx]; split=>//.
  exact:subset_closure (interior_subset hx).
have hSplit:=hMeas (closure S).
by rewrite hIntersection hNull adde0 in hSplit.
Qed.
