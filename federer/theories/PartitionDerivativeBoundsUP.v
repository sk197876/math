(** Federer (1969), 3.1.13, p. 225:
    constants V_i depending only on the dimension
    and the cutoff derivative constants G_0,...,G_i.
    The recurrence below is one explicit sufficient
    choice; Federer does not prescribe its values. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_partition_derivative_bounds]:
    a sufficient recursive choice of V_i
    for the last derivative estimate in
    Federer 3.1.13, p. 225.
    C will be 129^m. The recurrence
    comes from sigma*v_s=u_s and sigma>=1,
    using the Leibniz formula on p. 222. *)
Definition is_partition_derivative_bounds (R : realType)
    (C : R) (G V : nat->R) :=
  V 0%N= 1 /\ forall n,
    V n.+1=G n.+1+C*\sum_(j<n.+1)
      ('C(n.+1,n.+1-j))%:R*(G (n.+1-j)%N*V j).
