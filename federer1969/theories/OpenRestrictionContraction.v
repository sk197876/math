(** Federer (1969), 2.8.2, p. 142, reduction to finite-measure targets
    Intersect both the target and the testing open set with an open cover
    member. No measurability of the target is needed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import ContractionCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [contraction_selection_open_restriction]: Supporting Federer
    2.8.2, p. 142.A selection in W intersect U for A is the same selection
    in W for A intersect U. *)
Lemma contraction_selection_open_restriction (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (F : set (set X)) (A U W : set X)
    (q : R) (G : set (set X)) :
  is_contraction_cover_selection mu F A (W `&` U) q G ->
  is_contraction_cover_selection mu F (A `&` U) W q G.
Proof.
move=> h; constructor.
- exact: contraction_selection_members h.
- exact: contraction_selection_disjoint h.
- move=> x hx; exact: (contraction_selection_within h hx).1.
- have he : (W `&` (A `&` U)) = ((W `&` U) `&` A).
    apply/seteqP; split.
    * by move=> x [hw [ha hu]]; split=> //; split.
    * by move=> x [[hw hu] ha]; split=> //; split.
  rewrite he; exact: contraction_selection_bound h.
Qed.

(** Source for [local_contraction_open_restriction]: This is the
    finite-measure-target reduction in Federer 2.8.2, p. 142; it does not
    require A measurable. *)
Lemma local_contraction_open_restriction (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (F : set (set X)) (A U : set X) (q : R) :
  open U -> has_local_cover_contraction mu F A q ->
  has_local_cover_contraction mu F (A `&` U) q.
Proof.
move=> hU h W hW.
have [G [hG hs]] := h (W `&` U) (openI hW hU).
exists G; split=> //; exact: contraction_selection_open_restriction hs.
Qed.
