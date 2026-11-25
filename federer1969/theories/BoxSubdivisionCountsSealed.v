(** Opaque integer-count family supporting Federer (1969), 2.10.39, printed
    p. 199. Expose only the positive mesh, bracket and unsplit-axis laws.
    Source context: BoxSubdivisionCountsUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import BoxSubdivisionCountsUP BoxSubdivisionCountsConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type BOX_SUBDIVISION_COUNTS.
(** Source for [value]: abstract positive integer choices
    for the side subdivision in 2.10.39, p. 199. *)
Parameter value : forall (R : realType) n (c : 'I_n -> R) p (h : R),
  0<h -> (forall i : 'I_n, (i<p)%N -> h<=c i) -> 'I_n -> nat.
(** Source for [laws]: abstract count brackets and
    unsplit-axis laws supporting 2.10.39, p. 199. *)
Parameter laws : forall (R : realType) n (c : 'I_n -> R) p (h : R)
  (hh : 0<h) (hc : forall i : 'I_n, (i<p)%N -> h<=c i),
  is_box_subdivision_counts c p h (@value R n c p h hh hc).
End BOX_SUBDIVISION_COUNTS.
Module BoxSubdivisionCounts : BOX_SUBDIVISION_COUNTS.
(** Source for [value]: privately proved count witness
    supporting 2.10.39, p. 199, hidden by
    opaque module ascription. *)
Definition value (R : realType) n (c : 'I_n -> R) p (h : R)
  (hh : 0<h) (hc : forall i : 'I_n, (i<p)%N -> h<=c i) :=
  projT1 (cid (@box_subdivision_counts_exists R n c p h hh hc)).
(** Source for [laws]: proved integer-count laws for
    the box subdivision in 2.10.39, p. 199. *)
Lemma laws (R : realType) n (c : 'I_n -> R) p (h : R)
  (hh : 0<h) (hc : forall i : 'I_n, (i<p)%N -> h<=c i) :
  is_box_subdivision_counts c p h (@value R n c p h hh hc).
Proof. exact: (projT2 (cid (@box_subdivision_counts_exists R n c p h hh hc))). Qed.
End BoxSubdivisionCounts.
