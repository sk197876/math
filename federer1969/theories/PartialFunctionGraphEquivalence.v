(** Federer (1969), 2.3.2, pp. 73–74: supporting extensional reasoning for
    partial-function operations. Equivalent graphs give the same domains and
    inverse images, independently of the proof terms witnessing
    single-valuedness. Source context: PartialFunctionUP.v and
    MeasurableFunctionUP.v. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import PartialFunctionUP PartialFunctionPostcomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_function_equivalent_domains]: supporting
    graph-extensional domain law for Federer 2.3.2, p. 73. *)
Lemma partial_function_equivalent_domains (X Y : Type) (f g : partial_function X Y) :
  (forall x y, partial_function_graph f x y <-> partial_function_graph g x y) ->
  partial_function_domain f = partial_function_domain g.
Proof.
move=> he; apply/seteqP; split=> x [y hy]; exists y.
- exact: (proj1 (he x y) hy).
- exact: (proj2 (he x y) hy).
Qed.

(** Source for [partial_function_equivalent_preimages]: supporting
    graph-extensional inverse-image law for Federer 2.3.2, p. 73. *)
Lemma partial_function_equivalent_preimages (X Y : Type) (f g : partial_function X Y) :
  (forall x y, partial_function_graph f x y <-> partial_function_graph g x y) ->
  forall A, partial_function_preimage f A = partial_function_preimage g A.
Proof.
move=> he A; apply/seteqP; split=> x [y [hy ha]]; exists y; split=> //.
- exact: (proj1 (he x y) hy).
- exact: (proj2 (he x y) hy).
Qed.

(** Source for [partial_function_postcomposition_associative]:
    supporting graph law for repeated numerical postcomposition in
    Federer 2.3.2, p. 74, after (4)–(5). Explicit
    lambdas express ordinary composition without fixing unrelated
    universes through a global composition constant. *)
Lemma partial_function_postcomposition_associative (X Y Z W : Type)
    (f : partial_function X Y) (g : Y -> Z) (h : Z -> W) x w :
  partial_function_graph (partial_function_postcompose (partial_function_postcompose f g) h) x w <->
  partial_function_graph (partial_function_postcompose f (fun y => h (g y))) x w.
Proof.
split.
- move=> [z [[y [hy <-]] hw]]; by exists y.
- move=> [y [hy hw]]; exists (g y); split=> //; by exists y.
Qed.
