(** Federer (1969), 3.4.7, p. 325: evaluating
    the polynomial variable at the original xi germ
    identifies the transverse polynomial subring. The independent
    extension equations precede existence and injectivity proofs. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_commutative_polynomial_evaluation]: an
    evaluation homomorphism extends the original coefficients
    and takes the formal variable to the original
    selected element, supporting 3.4.7, p. 325. *)
Record is_commutative_polynomial_evaluation (A B C:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (phi:{rmorphism A->C}) (t:C)
    (evaluate:{rmorphism B->C}):Prop:={
  (** Source for [polynomial_evaluation_constants]: evaluation
      extends the original coefficient embedding, supporting
      3.4.7, p. 325. *)
  polynomial_evaluation_constants:forall a,evaluate (embed a) = phi a;
  (** Source for [polynomial_evaluation_variable]: the variable
      evaluates at the original chosen element, supporting
      3.4.7, p. 325. *)
  polynomial_evaluation_variable:evaluate variable = t
}.
