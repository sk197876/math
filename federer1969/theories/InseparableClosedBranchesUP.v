(** Federer (1969), 2.2.10, p. 67: assuming failure of separation, choose
    two nested closed branches whose images remain inseparable and whose
    diameters tend to zero. This specification records the branch sets C
    intersect E(m1,...,mk) and D intersect E(n1,...,nk). The existence
    construction refines those closed sets directly by the small covers of
    2.2.8, rather than storing unused siblings of the entire tree. Source
    editions: SuslinSetUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import BorelSeparation ClosedCoverTreeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_inseparable_closed_branches]: supporting
    abstract branch laws for Federer 2.2.10(1), p. 67.
    The roots are C and D, every branch set is closed and
    nonempty, descendants are nested, diameters shrink at the
    2.2.8 scale, and paired images fail to be Borel separated.
    These are witness laws to be proved, not project axioms. *)
Record is_inseparable_closed_branches (R : realType) (T : metricType R)
    (Y : topologicalType) (f : T -> Y) (C D : set T) (P Q : nat -> set T) : Prop := {
  inseparable_branches_left_root : P 0%N = C;
  inseparable_branches_right_root : Q 0%N = D;
  inseparable_branches_left_closed : forall n, closed (P n);
  inseparable_branches_right_closed : forall n, closed (Q n);
  inseparable_branches_left_nonempty : forall n, P n !=set0;
  inseparable_branches_right_nonempty : forall n, Q n !=set0;
  inseparable_branches_left_nested : forall n m, (n <= m)%N -> P m `<=` P n;
  inseparable_branches_right_nested : forall n m, (n <= m)%N -> Q m `<=` Q n;
  inseparable_branches_left_diameter : forall n x y,
    P n.+1 x -> P n.+1 y -> mdist x y <= @closed_cover_tree_scale R n;
  inseparable_branches_right_diameter : forall n x y,
    Q n.+1 x -> Q n.+1 y -> mdist x y <= @closed_cover_tree_scale R n;
  inseparable_branches_not_separated : forall n, ~ borel_separated (f @` P n) (f @` Q n)
}.
