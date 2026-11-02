(** Federer (1969), 2.4.18, pp. 90–91: compositions and image measures. Here
    u is total, as in Federer; f retains its possibly proper domain. The
    local Federer erratum contains no correction to this item. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_function_precompose]: supporting graph definition of
    f composed with u in Federer 2.4.18, p. 90 A source point has a value
    precisely when its image lies in the domain of f. *)
Definition partial_function_precompose (X Y Z : Type)
    (u : X -> Y) (f : partial_function Y Z) : partial_function X Z.
Proof.
refine (@Build_partial_function X Z (fun x z => partial_function_graph f (u x) z) _).
move=> x y z hy hz; exact: partial_function_single_valued hy hz.
Defined.

(** Source for [partial_function_precompose_domain]: Supporting Federer
    2.4.18, p. 90. *)
Lemma partial_function_precompose_domain (X Y Z : Type)
    (u : X -> Y) (f : partial_function Y Z) :
  partial_function_domain (partial_function_precompose u f) =
    u @^-1` (partial_function_domain f).
Proof. by []. Qed.

(** Source for [partial_function_precompose_preimage]: supporting
    inverse-image identity for Federer 2.4.18(1)–(2), pp. 90–91 *)
Lemma partial_function_precompose_preimage (X Y Z : Type)
    (u : X -> Y) (f : partial_function Y Z) (A : set Z) :
  partial_function_preimage (partial_function_precompose u f) A =
    u @^-1` (partial_function_preimage f A).
Proof. by []. Qed.

(** Source for [partial_function_precompose_total]: supporting
    total-function case of composition in Federer 2.4.18, p. 90 Equality is
    stated at the exposed graph rather than the record proof. *)
Lemma partial_function_precompose_total (X Y Z : Type)
    (u : X -> Y) (f : Y -> Z) x z :
  partial_function_graph (partial_function_precompose u (partial_function_total f)) x z <->
  partial_function_graph (partial_function_total (fun x => f (u x))) x z.
Proof. by []. Qed.

(** Source for [partial_function_precompose_postcompose]: supporting
    associativity used for positive and negative parts in the last case of
    Federer 2.4.18(1), proof p. 91 *)
Lemma partial_function_precompose_postcompose (X Y Z W : Type)
    (u : X -> Y) (f : partial_function Y Z) (g : Z -> W) x w :
  partial_function_graph (partial_function_precompose u (partial_function_postcompose f g)) x w <->
  partial_function_graph (partial_function_postcompose (partial_function_precompose u f) g) x w.
Proof. by []. Qed.
