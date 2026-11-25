(** Set-theoretic source restriction supporting the finite-average identity
    of Federer (1969), 2.3.8, p. 79, with partial domains retained as
    required by the erratum p. 1, book p. 78 line 7. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import PartialFunctionUP PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_function_source_restrict]: source restriction
    of a given graph, supporting the partial-domain interpretation
    of Federer 2.3.8, pp. 78–79; a set-theoretic operation. *)
Definition partial_function_source_restrict (X Y : Type) (A : set X)
    (f : partial_function X Y) : partial_function X Y.
Proof.
refine (@Build_partial_function X Y (fun x y => A x /\ partial_function_graph f x y) _).
move=> x y z [_ hy] [_ hz]; exact: partial_function_single_valued hy hz.
Defined.

(** Source for [partial_function_source_restrict_graph]: exact graph
    law for the source restriction supporting Federer 2.3.8,
    pp. 78–79, without assigning values outside the domain. *)
Lemma partial_function_source_restrict_graph (X Y : Type) (A : set X)
    (f : partial_function X Y) x y :
  partial_function_graph (partial_function_source_restrict A f) x y <->
    A x /\ partial_function_graph f x y.
Proof. by []. Qed.

(** Source for [partial_function_source_restrict_domain]: source
    restriction intersects the original domain with the restricting
    set, supporting Federer 2.3.8, pp. 78–79. *)
Lemma partial_function_source_restrict_domain (X Y : Type) (A : set X)
    (f : partial_function X Y) :
  partial_function_domain (partial_function_source_restrict A f) =
    A `&` partial_function_domain f.
Proof.
apply/seteqP; split=> x.
- move=> [y [hx hy]]; split=> //; by exists y.
- move=> [hx [y hy]]; exists y; by split.
Qed.

(** Source for [partial_function_source_restrict_agreement]: a
    restriction agrees with its original map precisely on their
    common domain; supporting almost equality in Federer 2.3.8,
    p. 78, through the convention of 2.3.1, p. 72. *)
Lemma partial_function_source_restrict_agreement (X Y : Type) (A : set X)
    (f : partial_function X Y) :
  partial_function_agreement f (partial_function_source_restrict A f) =
    A `&` partial_function_domain f.
Proof.
apply/seteqP; split=> x.
- move=> [y [hy [hx _]]]; split=> //; by exists y.
- move=> [hx [y hy]]; exists y; by split=> //; split.
Qed.
