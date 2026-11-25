(** Private existence witness for the geometric approximant in Federer
    (1969), proof of 2.4.4(2), p. 83. Integer cell coverage provides the
    positive values; the sealed interface exposes only the proved cell laws.
    Source context: GeometricQuantisationUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra ssrint boolp reals.
From Federer Require Import GeometricIntegerCells GeometricQuantisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [geometric_quantisation_exists]: existence of
    the cellwise geometric approximant in Federer 2.4.4(2),
    p. 83. Classical choice selects an integer only after
    coverage has been proved; downstream arguments use the laws. *)
Theorem geometric_quantisation_exists (R : realType) (t : R) :
  1 < t -> exists q : R -> R, is_geometric_quantisation t q.
Proof.
move=> ht.
have hex x : exists y : R,
    (x <= 0 -> y=0) /\
    (0 < x -> exists j : int, t^j <= x /\ x < t^(j+1) /\ y=t^j).
  have [hx|hx] := leP x 0.
  - exists 0; split=> // hp; by move: hp; rewrite ltNge hx.
  - have [j [hl hu]] := @geometric_integer_cell_exists R t x ht hx.
    exists (t^j); split.
    + by move=> hfalse; discriminate hfalse.
    + move=> _; exists j; by split=> //; split.
pose q x := projT1 (cid (hex x)).
have hq x := projT2 (cid (hex x)).
exists q; split=> x; [exact: (hq x).1|exact: (hq x).2].
Qed.
