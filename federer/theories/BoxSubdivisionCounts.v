(** Public abstract subdivision counts supporting Federer (1969), 2.10.39,
    printed p. 199. The construction is hidden; later cost bounds use only
    the count brackets. Source context: BoxSubdivisionCountsUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import BoxSubdivisionCountsUP BoxSubdivisionCountsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [box_subdivision_counts]: abstract chosen
    positive integer family for the subdivision in
    2.10.39, p. 199. *)
Definition box_subdivision_counts (R : realType) n (c : 'I_n -> R) p (h : R)
    (hh : 0<h) (hc : forall i : 'I_n, (i<p)%N -> h<=c i) :=
  @BoxSubdivisionCounts.value R n c p h hh hc.

(** Source for [box_subdivision_counts_specification]: proved
    positive-count, bracket and unsplit-axis laws for
    the box subdivision in 2.10.39, p. 199. *)
Theorem box_subdivision_counts_specification (R : realType) n (c : 'I_n -> R) p (h : R)
    (hh : 0<h) (hc : forall i : 'I_n, (i<p)%N -> h<=c i) :
  is_box_subdivision_counts c p h (@box_subdivision_counts R n c p h hh hc).
Proof. exact: BoxSubdivisionCounts.laws. Qed.
