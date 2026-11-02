(** Opaque equal-cost child length for Federer (1969), 2.10.28(4), p. 192.
    Only the proved construction is imported here; downstream proofs use its
    defining cost and strict bounds. Source context and the nondegeneracy
    correction are recorded in CantorSplitRadiusUP.v. *)
(** Federer 2.10.28, pp. 192–193: source context and the abstract laws are
    recorded in the corresponding specification module. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ConcaveIntervalGaugeUP CantorSplitRadiusUP CantorSplitRadiusConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Module Type CANTOR_SPLIT_RADIUS.
(** Source for [value]: abstract equal-cost child
    length in 2.10.28(4), p. 192,
    for a positive parent length and n>=2. *)
Parameter value : forall (R : realType) (h : R -> R),
  is_concave_interval_gauge h -> forall (d : R) (n : nat), 0<d -> (2<=n)%N -> R.
(** Source for [laws]: defining bounds and cost
    of the child length in 2.10.28(4),
    p. 192, supplied by a proved witness. *)
Parameter laws : forall (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h)
  (d : R) (n : nat) (hd : 0<d) (hn : (2<=n)%N),
  is_cantor_split_radius h d n (@value R h hg d n hd hn).
End CANTOR_SPLIT_RADIUS.

Module CantorSplitRadius : CANTOR_SPLIT_RADIUS.
(** Source for [value]: proved existence witness
    of the equal-cost child length in 2.10.28(4),
    p. 192, hidden by opaque module ascription. *)
Definition value (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h)
    (d : R) (n : nat) (hd : 0<d) (hn : (2<=n)%N) :=
  projT1 (cid (@cantor_split_radius_exists R h hg d n hd hn)).
(** Source for [laws]: abstract child-length laws
    in 2.10.28(4), p. 192, from
    the proved intermediate-value construction. *)
Lemma laws (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h)
    (d : R) (n : nat) (hd : 0<d) (hn : (2<=n)%N) :
  is_cantor_split_radius h d n (@value R h hg d n hd hn).
Proof. exact: (projT2 (cid (@cantor_split_radius_exists R h hg d n hd hn))). Qed.
End CantorSplitRadius.
