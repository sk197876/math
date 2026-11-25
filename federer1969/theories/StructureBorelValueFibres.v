(** Supporting Federer (1969), 3.3.4,
    p. 289: exact zero and infinite
    values of an extended-real Borel
    density have Borel parameter fibres. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology CountableOrderIntervals
  BorelFunctionUP BorelFunctionBasic TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_borel_value_fibre]: exact
    density-value fibres used for B_j and
    C_j in Federer 3.3.4, p. 289,
    through the Borel density of 3.3.2,
    pp. 287–288. Each value singleton
    is an intersection of two closed
    order rays, including either infinity. *)
Theorem structure_borel_value_fibre (R:realType) (P:topologicalType)
    (f:P->extended_real_line R) (c: \bar R):
  is_borel_function f ->borel_set [set x:P|f x=c].
Proof.
move=>hF.
have hEqual:[set y:extended_real_line R|y=c]=
    [set y|(y<=c)%E] `&` [set y|(c<=y)%E].
  apply/seteqP; split=>y.
  - move=>->; by split; exact:lexx.
  - move=>[hL hU]; apply/eqP; by rewrite eq_le hL hU.
have hSingleton:borel_set [set y:extended_real_line R|y=c].
  rewrite hEqual; apply:(borel_family_binary_intersection (borel_sets_family (extended_real_line R))).
  - apply:closed_borel_set; exact:(@order_closed_lower_ray_closed _
      [the orderTopologicalType _ of order_topology (\bar R)] c).
  - apply:closed_borel_set; exact:(@order_closed_upper_ray_closed _
      [the orderTopologicalType _ of order_topology (\bar R)] c).
exact:(borel_function_preimage hF hSingleton).
Qed.
