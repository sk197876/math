(** Federer (1969), 2.3.1, p. 72: functions specified by their
    single-valued graphs. Supporting source-dependent postcomposition
    for the actual differential expressions in 3.1.1, p. 211, and
    the tensor-speed integral of 3.2.46, p. 281. No value is supplied
    outside the original domain. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_function_source_postcompose]: supporting
    graph composition in the function convention of Federer 2.3.1,
    p. 72. At an actual pair (x,y) of f, the new value is h(x,y). *)
Definition partial_function_source_postcompose (X Y Z : Type)
    (f : partial_function X Y) (h : X -> Y -> Z) : partial_function X Z.
Proof.
refine (@Build_partial_function X Z
  (fun x z => exists y, partial_function_graph f x y /\ h x y = z) _).
move=> x z w [y [hy <-]] [v [hv <-]].
by rewrite (partial_function_single_valued hy hv).
Defined.

(** Source for [partial_function_source_postcompose_graph]: exact
    graph law for the composition supporting Federer 2.3.1, p. 72,
    and the scalar differential tests of 3.1.1, p. 211. *)
Lemma partial_function_source_postcompose_graph (X Y Z : Type)
    (f : partial_function X Y) (h : X -> Y -> Z) x z :
  partial_function_graph (partial_function_source_postcompose f h) x z <->
    exists y, partial_function_graph f x y /\ h x y = z.
Proof. by []. Qed.

(** Source for [partial_function_source_postcompose_domain]: the
    original domain is preserved, supporting the exact-domain
    convention in Federer 2.3.1, p. 72, and 3.1.1, p. 211. *)
Lemma partial_function_source_postcompose_domain (X Y Z : Type)
    (f : partial_function X Y) (h : X -> Y -> Z) :
  partial_function_domain (partial_function_source_postcompose f h) =
    partial_function_domain f.
Proof.
apply/seteqP; split=> x.
- by move=> [z [y [hy _]]]; exists y.
- move=> [y hy]; exists (h x y); by exists y; split.
Qed.
