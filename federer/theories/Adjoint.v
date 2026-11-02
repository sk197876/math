(** Federer (1969), 1.7.4, p. 30: public adjoint interface, supporting also
    the final factorisation of 1.7.3. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP LinearBasis AdjointUP AdjointSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Interface.
Variable R : rcfType.
Variables V U : lmodType R.
Variable B : V -> V -> R.
Variable C : U -> U -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable f : {linear V -> U}.

(** Source for [inner_adjoint]: Federer 1.7.4, p. 30,
    the adjoint linear map supplied by the sealed interface. *)
Definition inner_adjoint : {linear U -> V} := @Adjoint.map R V U B C hB hC n b hb f.

(** Source for [inner_adjointP]: Federer 1.7.4, p. 30,
    the adjoint satisfies x.f*(y)=f(x).y. *)
Theorem inner_adjointP : is_adjoint B C f inner_adjoint.
Proof. exact: Adjoint.laws. Qed.
End Interface.
