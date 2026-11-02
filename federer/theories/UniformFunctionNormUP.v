(** Federer (1969), 2.5.19, p. 113, norm nu(f)=sup im |f|, used for the
    dense extension in 2.6.6, p. 120. The equivalent least-nonnegative-bound
    specification includes the zero norm on an empty domain. It specifies
    laws, not an unproved existence axiom. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_uniform_function_norm]: equivalent least-bound
    definition of nu(f) in Federer 2.5.19, p. 113; used in 2.6.6,
    p. 120. Requiring a nonnegative bound specifies zero when X
    is empty, where a bare real supremum needs a convention. *)
Record is_uniform_function_norm (R : realType) (X : Type) (f : X -> R) (n : R) : Prop := {
  (** Source for [uniform_function_norm_nonnegative]: nonnegativity
      of the uniform norm, Federer 2.5.19, p. 113. *)
  uniform_function_norm_nonnegative : 0<=n;
  (** Source for [uniform_function_norm_bound]: evaluation bound
      from the supremum defining nu, Federer 2.5.19, p. 113. *)
  uniform_function_norm_bound : forall x, `|f x|<=n;
  (** Source for [uniform_function_norm_least]: least-bound property
      of the supremum in Federer 2.5.19, p. 113. *)
  uniform_function_norm_least : forall c, 0<=c -> (forall x, `|f x|<=c) -> n<=c
}.

(** Source for [uniform_function_norm_unique]: supporting uniqueness
    of the uniform norm used in Federer 2.6.6, p. 120. *)
Lemma uniform_function_norm_unique (R : realType) (X : Type) (f : X -> R) n m :
  is_uniform_function_norm f n -> is_uniform_function_norm f m -> n=m.
Proof.
move=> hn hm; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (@uniform_function_norm_least R X f n hn m) (uniform_function_norm_nonnegative hm) (uniform_function_norm_bound hm).
- exact: (@uniform_function_norm_least R X f m hm n) (uniform_function_norm_nonnegative hn) (uniform_function_norm_bound hn).
Qed.
