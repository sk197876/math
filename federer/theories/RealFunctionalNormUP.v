(** Federer (1969), 2.4.12, p. 87: the continuous real dual is endowed with
    the supremum norm on the closed unit ball. This equivalent least-bound
    specification avoids choosing a supremum implementation. Norms are
    finite-valued and spaces need not be finite dimensional. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_real_functional_norm]: equivalent abstract
    specification of the dual norm in Federer 2.4.12, p. 87.
    It is the least nonnegative constant bounding all evaluations. *)
Record is_real_functional_norm (R : realType) (V : lmodType R)
    (N : V -> R) (a : {linear V -> R^o}) (n : R) : Prop := {
  (** Source for [real_functional_norm_nonnegative]: nonnegativity
      of the dual norm in Federer 2.4.12, p. 87. *)
  real_functional_norm_nonnegative : 0 <= n;
  (** Source for [real_functional_norm_bound]: the evaluation bound
      associated with the dual norm in Federer 2.4.12, p. 87. *)
  real_functional_norm_bound : forall y, `|a y| <= n*N y;
  (** Source for [real_functional_norm_least]: least-bound property
      of the supremum defining the dual norm, Federer 2.4.12, p. 87. *)
  real_functional_norm_least : forall C, 0 <= C ->
    (forall y, `|a y| <= C*N y) -> n <= C
}.

(** Source for [real_functional_norm_unique]: supporting uniqueness
    of the dual norm specified in Federer 2.4.12, p. 87. *)
Lemma real_functional_norm_unique (R : realType) (V : lmodType R)
    (N : V -> R) (a : {linear V -> R^o}) n m :
  is_real_functional_norm N a n -> is_real_functional_norm N a m -> n = m.
Proof.
move=> hn hm; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (real_functional_norm_least hn (real_functional_norm_nonnegative hm) (real_functional_norm_bound hm)).
- exact: (real_functional_norm_least hm (real_functional_norm_nonnegative hn) (real_functional_norm_bound hn)).
Qed.
