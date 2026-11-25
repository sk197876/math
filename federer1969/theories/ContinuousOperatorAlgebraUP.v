(** Federer (1969), 3.1.11, p. 220:
    the continuous endomorphisms of a normed space, with
    composition, identity and the operator norm. The algebra
    uses the existing unital associative algebra specification,
    which also permits the zero vector space. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Hom AlgebraUP ContinuousOperatorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.

(** Source for [is_continuous_operator_algebra]: the normed
    algebra E of all continuous linear endomorphisms in
    Federer 3.1.11, p. 220. Evaluation identifies
    its multiplication and unit with composition and identity;
    all carrier and norm laws remain abstract. *)
Record is_continuous_operator_algebra (R : realType) (X : lmodType R)
    (NX : X->R) (A : algebra R)
    (evaluation : Hom A (Hom X X)) (AN : A->R) : Prop := {
  (** Source for [operator_algebra_space]: E contains exactly
      the continuous endomorphisms with their operator norm,
      Federer 3.1.11, p. 220. *)
  operator_algebra_space : is_continuous_operator_space NX NX evaluation AN;
  (** Source for [operator_algebra_identity]: the algebra unit
      evaluates as the identity on X, supporting the
      inverse series in Federer 3.1.11, p. 220. *)
  operator_algebra_identity : evaluation (alg_one A)=hom_of_linear (linear_id X);
  (** Source for [operator_algebra_composition]: multiplication
      evaluates as composition of operators, Federer
      3.1.11, p. 220. *)
  operator_algebra_composition : forall u v,
    evaluation (alg_mul A u v)=hom_comp (evaluation u) (evaluation v)
}.
