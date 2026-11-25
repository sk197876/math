(** Federer (1969), 2.3.2(4), p. 73: set-theoretic composition of a partial
    function with a total function. These graph laws support the measurable
    composition theorem. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_function_postcompose]: supporting ordinary
    graph definition of the composition in Federer 2.3.2(4),
    p. 73. It keeps exactly the domain of f. *)
Definition partial_function_postcompose (X Y Z : Type)
    (f : partial_function X Y) (g : Y -> Z) : partial_function X Z.
Proof.
refine (@Build_partial_function X Z (fun x z => exists y,
  partial_function_graph f x y /\ g y = z) _).
move=> x z w [y [hy <-]] [v [hv <-]].
by rewrite (partial_function_single_valued hy hv).
Defined.

(** Source for [partial_function_postcompose_domain]: supporting
    domain preservation in Federer 2.3.2(4), p. 73. *)
Lemma partial_function_postcompose_domain (X Y Z : Type)
    (f : partial_function X Y) (g : Y -> Z) :
  partial_function_domain (partial_function_postcompose f g) = partial_function_domain f.
Proof.
apply/seteqP; split=> x.
- by move=> [z [y [hy _]]]; exists y.
- by move=> [y hy]; exists (g y); exists y.
Qed.

(** Source for [partial_function_postcompose_preimage]: supporting
    inverse-image identity in Federer 2.3.2(4), p. 73 *)
Lemma partial_function_postcompose_preimage (X Y Z : Type)
    (f : partial_function X Y) (g : Y -> Z) (A : set Z) :
  partial_function_preimage (partial_function_postcompose f g) A =
  partial_function_preimage f [set y | A (g y)].
Proof.
apply/seteqP; split=> x.
- move=> [z [[y [hy <-]] ha]]; by exists y.
- move=> [y [hy ha]]; exists (g y); split=> //; by exists y.
Qed.
