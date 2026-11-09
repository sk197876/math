(** Federer (1969), 3.4.5, p. 319: the actual
    analytic germs form a commutative ring with unit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric LocalGermUP LocalGermEquivalence LocalGermSealed
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RingLaws.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation P:=(@analytic_representative_type R X NX hNX a).
Local Notation value:=(@analytic_representative_value R X NX hNX a).
Local Notation G:=(analytic_germ_space hNX a).
Local Notation germ:=(@analytic_germ R X NX hNX a).
Local Notation add:=(@AnalyticGerms.add R X NX hNX a).
Local Notation mul:=(@AnalyticGerms.mul R X NX hNX a).
Local Notation opp:=(@AnalyticGerms.opp R X NX hNX a).
Local Notation zero:=(@analytic_germ_zero R X NX hNX a).
Local Notation one:=(@analytic_germ_one R X NX hNX a).

(** Source for [analytic_germ_has_representative]: each class
    in the ring of 3.4.5, p. 319, has an actual
    analytic representative. Downstream proofs use only the sealed laws. *)
Lemma analytic_germ_has_representative (alpha:G):exists f:P,germ f=alpha.
Proof.
exact:(@local_germ_representative (Topological.clone (real_norm_metric_space hNX) _) R
  P value a G germ (@LocalGerms.laws (Topological.clone (real_norm_metric_space hNX) _) R P value a) alpha).
Qed.

(** Source for [analytic_germ_pointwise_equality]: globally equal
    representatives define the same analytic germ, 3.4.5, p. 319. *)
Lemma analytic_germ_pointwise_equality (f g:P):
  (forall x,value f x=value g x) ->germ f=germ g.
Proof.
move=>hEq;apply/(local_germ_equality (@LocalGerms.laws (Topological.clone (real_norm_metric_space hNX) _) R P value a)).
exact:(@locally_equal_global (Topological.clone (real_norm_metric_space hNX) _) R a (value f) (value g) hEq).
Qed.

(** Source for [analytic_germ_equal_at_centre]: the zeroth
    derivative is determined by the germ, 3.4.5, p. 319. *)
Lemma analytic_germ_equal_at_centre (f g:P):germ f=germ g ->value f a=value g a.
Proof.
move/(local_germ_equality (@LocalGerms.laws (Topological.clone (real_norm_metric_space hNX) _) R P value a))=>[U [hU [ha hEq]]].
exact:hEq a ha.
Qed.

(** Source for [analytic_germ_add_associative]: associativity
    inherited from functional addition, 3.4.5, p. 319. *)
Lemma analytic_germ_add_associative:associative add.
Proof.
move=>alpha beta gamma.
have [f <-]:=analytic_germ_has_representative alpha.
have [g <-]:=analytic_germ_has_representative beta.
have [h <-]:=analytic_germ_has_representative gamma.
rewrite !(@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
apply:analytic_germ_pointwise_equality=>x;exact:addrA.
Qed.

(** Source for [analytic_germ_add_commutative]: commutativity
    inherited from functional addition, 3.4.5, p. 319. *)
Lemma analytic_germ_add_commutative:commutative add.
Proof.
move=>alpha beta.
have [f <-]:=analytic_germ_has_representative alpha.
have [g <-]:=analytic_germ_has_representative beta.
rewrite !(@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
apply:analytic_germ_pointwise_equality=>x;exact:addrC.
Qed.

(** Source for [analytic_germ_add_zero]: the zero germ is
    the additive identity, 3.4.5, p. 319. *)
Lemma analytic_germ_add_zero:left_id zero add.
Proof.
move=>alpha;have [f <-]:=analytic_germ_has_representative alpha.
rewrite /analytic_germ_zero
  (@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
apply:analytic_germ_pointwise_equality=>x;exact:add0r.
Qed.

(** Source for [analytic_germ_add_negate]: negation supplies
    additive inverses, 3.4.5, p. 319. *)
Lemma analytic_germ_add_negate:left_inverse zero opp add.
Proof.
move=>alpha;have [f <-]:=analytic_germ_has_representative alpha.
rewrite (@analytic_germ_negate_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a))
  (@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)) /analytic_germ_zero.
apply:analytic_germ_pointwise_equality=>x;exact:addNr.
Qed.

(** Source for [analytic_germ_multiply_associative]: functional
    multiplication is associative on germs, 3.4.5, p. 319. *)
Lemma analytic_germ_multiply_associative:associative mul.
Proof.
move=>alpha beta gamma.
have [f <-]:=analytic_germ_has_representative alpha.
have [g <-]:=analytic_germ_has_representative beta.
have [h <-]:=analytic_germ_has_representative gamma.
rewrite !(@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
apply:analytic_germ_pointwise_equality=>x;exact:mulrA.
Qed.

(** Source for [analytic_germ_multiply_commutative]: functional
    multiplication is commutative on germs, 3.4.5, p. 319. *)
Lemma analytic_germ_multiply_commutative:commutative mul.
Proof.
move=>alpha beta.
have [f <-]:=analytic_germ_has_representative alpha.
have [g <-]:=analytic_germ_has_representative beta.
rewrite !(@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
apply:analytic_germ_pointwise_equality=>x;exact:mulrC.
Qed.

(** Source for [analytic_germ_multiply_one]: the constant-one
    germ is the multiplicative identity, 3.4.5, p. 319. *)
Lemma analytic_germ_multiply_one:left_id one mul.
Proof.
move=>alpha;have [f <-]:=analytic_germ_has_representative alpha.
rewrite /analytic_germ_one
  (@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
apply:analytic_germ_pointwise_equality=>x;exact:mul1r.
Qed.

(** Source for [analytic_germ_distributive]: multiplication
    distributes over addition in the ring, 3.4.5, p. 319. *)
Lemma analytic_germ_distributive:left_distributive mul add.
Proof.
move=>alpha beta gamma.
have [f <-]:=analytic_germ_has_representative alpha.
have [g <-]:=analytic_germ_has_representative beta.
have [h <-]:=analytic_germ_has_representative gamma.
rewrite !(@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a))
  !(@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a))
  !(@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
apply:analytic_germ_pointwise_equality=>x;exact:mulrDl.
Qed.

(** Source for [analytic_germ_one_not_zero]: the unit and zero
    are distinct in the original analytic ring, 3.4.5, p. 319. *)
Lemma analytic_germ_one_not_zero:one!=zero.
Proof.
apply/eqP=>hEqual.
have hValue:=analytic_germ_equal_at_centre hEqual.
change ((1:R)=0) in hValue.
by move:(oner_neq0 R);rewrite hValue eqxx.
Qed.
End RingLaws.
