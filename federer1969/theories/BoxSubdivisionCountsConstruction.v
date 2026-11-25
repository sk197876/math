(** Private integer-count witness for Federer (1969), 2.10.39, printed p.
    199. Choose a scalar bracket on every long axis and one cell on every
    other axis. The resulting family is exposed only by its proved count
    laws through an opaque interface. Source context:
    BoxSubdivisionCountsUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ScalarSubdivisionCount BoxSubdivisionCountsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [box_subdivision_counts_exists]: private
    positive integer choices in 2.10.39, p. 199.
    Every long side has length at least the positive
    mesh; the stronger strict scalar bracket supplies
    the weak public upper law. *)
Theorem box_subdivision_counts_exists (R : realType) n
    (c : 'I_n -> R) p (h : R) :
  0<h -> (forall i : 'I_n, (i<p)%N -> h<=c i) ->
  exists count, is_box_subdivision_counts c p h count.
Proof.
move=> hh hc.
have hex (i : 'I_n) : exists k : nat, (0<k)%N /\
    ((i<p)%N -> c i<=k%:R*h /\ k%:R*h<=2*c i) /\
    ((p<=i)%N -> k= 1%N).
  case: (ltnP i p)=> hi.
  - have [k [hk [hlo hhi]]] := positive_mesh_subdivision_count hh (hc i hi).
    exists k; split=> //; split; first by move=> _; split=> //; exact: ltW hhi.
    by move=> hfalse; exfalso; exact (notF hfalse).
  - by exists 1%N; split=> //; split=> //.
pose count i := projT1 (cid (hex i)).
have hcount i := projT2 (cid (hex i)).
exists count; constructor=> //.
- move=> i; exact: (hcount i).1.
- move=> i hi; exact: (hcount i).2.1 hi.
- move=> i hi; exact: (hcount i).2.2 hi.
Qed.
