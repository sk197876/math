(** Federer (1969), 2.10.28(1), proof p. 192: supporting laws for the left
    and right boundary members of a finite disjoint interval family clipped
    by [a,b]. A missing boundary member contributes the degenerate endpoint
    interval, of cost h(0)=0. This avoids assuming that a or b belongs to
    the original family. No interval may contain the whole test interval in
    this reduction; that separate case is immediate. The endpoint
    placeholders give the same two enlargement inequalities without that
    shrinkage. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.

(** Source for [is_finite_interval_boundary]: supporting
    endpoint data for the two enlargement steps
    in 2.10.28(1), p. 192. Optional
    indices distinguish actual members from zero-cost
    degenerate placeholders; this is auxiliary proof
    infrastructure, not an extra book hypothesis. *)
Record is_finite_interval_boundary (R : realType) (I : choiceType) (F : {fset I})
    (l r : I -> R) (a b : R) (L W : option I) (v0 v1 w0 w1 : R) : Prop := {
  (** Source for [finite_interval_boundary_order]: supporting
      order of the two boundary members and the
      test interval in 2.10.28(1), p. 192. *)
  finite_interval_boundary_order : v0<=a /\ a<=v1 /\ v1<=w0 /\ w0<=b /\ b<=w1;
  (** Source for [finite_interval_boundary_left]: supporting
      actual left member or endpoint placeholder
      in the enlargement argument, 2.10.28(1),
      p. 192. *)
  finite_interval_boundary_left : match L with
    | Some i => i \in F /\ v0=l i /\ v1=r i
    | None => v0=a /\ v1=a
    end;
  (** Source for [finite_interval_boundary_right]: supporting
      actual right member or endpoint placeholder
      in the enlargement argument, 2.10.28(1),
      p. 192. *)
  finite_interval_boundary_right : match W with
    | Some i => i \in F /\ w0=l i /\ w1=r i
    | None => w0=b /\ w1=b
    end;
  (** Source for [finite_interval_boundary_left_detection]:
      supporting uniqueness of the member meeting
      a in a disjoint closed family in
      2.10.28(1), p. 192. *)
  finite_interval_boundary_left_detection : forall i, i \in F -> l i<=a -> a<=r i -> L=Some i;
  (** Source for [finite_interval_boundary_right_detection]:
      supporting uniqueness of the member meeting
      b in a disjoint closed family in
      2.10.28(1), p. 192. *)
  finite_interval_boundary_right_detection : forall i, i \in F -> l i<=b -> b<=r i -> W=Some i
}.
