(** Federer (1969), 3.1.2, p. 212: values outside the actual domain
    do not affect approximate differentials or approximate partial derivatives.
    These supporting laws justify use of a total representative on that domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates RealNormUP
  NormMetric RealMetricBackground PartialFunctionUP ApproximateDifferentialUP
  ApproximateDifferentialRemainder ApproximatePartialDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [approximate_differential_domain_agreement]: the map
    f:A -> Y in Federer 3.1.2, p. 212, is used only on A, including
    the base point. Changing a total representative outside A preserves
    the exact approximate-differentiability condition. *)
Theorem approximate_differential_domain_agreement (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (A : R_n R n -> Prop) (f g : R_n R n -> Y) a L :
  (forall x, A x -> f x=g x) ->
  (has_approximate_differential NY A f a L <->
   has_approximate_differential NY A g a L).
Proof.
move=> hfg.
have he (ha : A a) x q :
    partial_function_graph (approximate_remainder_quotient NY A f a L) x q <->
    partial_function_graph (approximate_remainder_quotient NY A g a L) x q.
  rewrite !approximate_remainder_quotient_graph.
  split; move=> [hx [hne hq]]; split=> //; split=> //.
  - by rewrite -(hfg x hx) -(hfg a ha).
  - by rewrite (hfg x hx) (hfg a ha).
have hp (ha : A a) W : partial_function_preimage (approximate_remainder_quotient NY A f a L) W=
    partial_function_preimage (approximate_remainder_quotient NY A g a L) W.
  apply/seteqP; split=> x [q [hq hW]]; exists q; split=> //.
  - exact: (he ha x q).1 hq.
  - exact: (he ha x q).2 hq.
split; move=> [ha hl]; split=> // W hW.
- rewrite -(hp ha W); exact: hl W hW.
- rewrite (hp ha W); exact: hl W hW.
Qed.

(** Source for [approximate_partial_quotient_graph]: actual-domain
    interpretation of the coordinate quotient in Federer 3.1.2, p. 212.
    Nonzero scalar increments and membership of the coordinate point
    are both explicit. *)
Lemma approximate_partial_quotient_graph (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) a i t v :
  partial_function_graph (approximate_partial_quotient hNY A f a i) t v <->
    t!=0 /\ A (a+t*:(@coordinate_basis R n i)) /\
      v=t^-1*:(f (a+t*:(@coordinate_basis R n i))-f a).
Proof.
split.
- move=> [[ht hx] <-]; by split=> //; split.
- move=> [ht [hx ->]]; by split; [split|].
Qed.

(** Source for [approximate_partial_derivative_domain_agreement]:
    supporting domain-independence law for ap D_i f in Federer 3.1.2,
    p. 212. Only values at the base point and actual coordinate-domain
    points enter its defining approximate limit. *)
Theorem approximate_partial_derivative_domain_agreement (R : realType) n
    (Y : lmodType R) (NY : Y -> R) (hNY : is_real_norm NY)
    (A : R_n R n -> Prop) (f g : R_n R n -> Y) a i v :
  (forall x, A x -> f x=g x) ->
  (has_approximate_partial_derivative hNY A f a i v <->
   has_approximate_partial_derivative hNY A g a i v).
Proof.
move=> hfg.
have he (ha : A a) t q :
    partial_function_graph (approximate_partial_quotient hNY A f a i) t q <->
    partial_function_graph (approximate_partial_quotient hNY A g a i) t q.
  rewrite !approximate_partial_quotient_graph.
  split; move=> [ht [hx hq]]; split=> //; split=> //.
  - by rewrite -(hfg _ hx) -(hfg a ha).
  - by rewrite (hfg _ hx) (hfg a ha).
have hp (ha : A a) W : partial_function_preimage (approximate_partial_quotient hNY A f a i) W=
    partial_function_preimage (approximate_partial_quotient hNY A g a i) W.
  apply/seteqP; split=> x [q [hq hW]]; exists q; split=> //.
  - exact: (he ha x q).1 hq.
  - exact: (he ha x q).2 hq.
split; move=> [ha hl]; split=> // W hW.
- rewrite -(hp ha W); exact: hl W hW.
- rewrite (hp ha W); exact: hl W hW.
Qed.
