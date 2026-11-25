(** Federer (1969), 3.4.12, p. 339: the actual
    holomorphic germs form a commutative ring with unit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed NormMetric LocalGermUP LocalGermEquivalence LocalGermSealed
  HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives
  HolomorphicGermUP HolomorphicGermOperationsUP HolomorphicGermSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RingLaws.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Variable NX:XR->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation P:=(@holomorphic_representative_type R X NX hNX a).
Local Notation value:=(@holomorphic_representative_value R X NX hNX a).
Local Notation G:=(holomorphic_germ_space hNX a).
Local Notation germ:=(@holomorphic_germ R X NX hNX a).
Local Notation add:=(@HolomorphicGerms.add R X NX hNX a).
Local Notation mul:=(@HolomorphicGerms.mul R X NX hNX a).
Local Notation opp:=(@HolomorphicGerms.opp R X NX hNX a).
Local Notation zero:=(@holomorphic_germ_zero R X NX hNX a).
Local Notation one:=(@holomorphic_germ_one R X NX hNX a).

(** Source for [holomorphic_germ_has_representative]: each class
    in the ring of 3.4.12, p. 339, has an actual
    holomorphic representative. Downstream proofs use only the sealed laws. *)
Lemma holomorphic_germ_has_representative (alpha:G):exists f:P,germ f=alpha.
Proof.
exact:(@local_germ_representative (Topological.clone (real_norm_metric_space hNX) _) C
  P value a G germ (@LocalGerms.laws (Topological.clone (real_norm_metric_space hNX) _) C P value a) alpha).
Qed.

(** Source for [holomorphic_germ_pointwise_equality]: globally equal
    representatives define the same holomorphic germ, 3.4.12, p. 339. *)
Lemma holomorphic_germ_pointwise_equality (f g:P):
  (forall x,value f x=value g x) ->germ f=germ g.
Proof.
move=>hEq;apply/(local_germ_equality (@LocalGerms.laws (Topological.clone (real_norm_metric_space hNX) _) C P value a)).
exact:(@locally_equal_global (Topological.clone (real_norm_metric_space hNX) _) C a (value f) (value g) hEq).
Qed.

(** Source for [holomorphic_germ_equal_at_centre]: the zeroth
    derivative is determined by the germ, 3.4.12, p. 339. *)
Lemma holomorphic_germ_equal_at_centre (f g:P):germ f=germ g ->value f a=value g a.
Proof.
move/(local_germ_equality (@LocalGerms.laws (Topological.clone (real_norm_metric_space hNX) _) C P value a))=>[U [hU [ha hEq]]].
exact:hEq a ha.
Qed.

(** Source for [holomorphic_germ_add_associative]: associativity
    inherited from functional addition, 3.4.12, p. 339. *)
Lemma holomorphic_germ_add_associative:associative add.
Proof.
move=>alpha beta gamma.
have [f <-]:=holomorphic_germ_has_representative alpha.
have [g <-]:=holomorphic_germ_has_representative beta.
have [h <-]:=holomorphic_germ_has_representative gamma.
rewrite !(@holomorphic_germ_add_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
apply:holomorphic_germ_pointwise_equality=>x;exact:addrA.
Qed.

(** Source for [holomorphic_germ_add_commutative]: commutativity
    inherited from functional addition, 3.4.12, p. 339. *)
Lemma holomorphic_germ_add_commutative:commutative add.
Proof.
move=>alpha beta.
have [f <-]:=holomorphic_germ_has_representative alpha.
have [g <-]:=holomorphic_germ_has_representative beta.
rewrite !(@holomorphic_germ_add_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
apply:holomorphic_germ_pointwise_equality=>x;exact:addrC.
Qed.

(** Source for [holomorphic_germ_add_zero]: the zero germ is
    the additive identity, 3.4.12, p. 339. *)
Lemma holomorphic_germ_add_zero:left_id zero add.
Proof.
move=>alpha;have [f <-]:=holomorphic_germ_has_representative alpha.
rewrite /holomorphic_germ_zero
  (@holomorphic_germ_add_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
apply:holomorphic_germ_pointwise_equality=>x;exact:add0r.
Qed.

(** Source for [holomorphic_germ_add_negate]: negation supplies
    additive inverses, 3.4.12, p. 339. *)
Lemma holomorphic_germ_add_negate:left_inverse zero opp add.
Proof.
move=>alpha;have [f <-]:=holomorphic_germ_has_representative alpha.
rewrite (@holomorphic_germ_negate_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a))
  (@holomorphic_germ_add_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)) /holomorphic_germ_zero.
apply:holomorphic_germ_pointwise_equality=>x;exact:addNr.
Qed.

(** Source for [holomorphic_germ_multiply_associative]: functional
    multiplication is associative on germs, 3.4.12, p. 339. *)
Lemma holomorphic_germ_multiply_associative:associative mul.
Proof.
move=>alpha beta gamma.
have [f <-]:=holomorphic_germ_has_representative alpha.
have [g <-]:=holomorphic_germ_has_representative beta.
have [h <-]:=holomorphic_germ_has_representative gamma.
rewrite !(@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
apply:holomorphic_germ_pointwise_equality=>x;exact:mulrA.
Qed.

(** Source for [holomorphic_germ_multiply_commutative]: functional
    multiplication is commutative on germs, 3.4.12, p. 339. *)
Lemma holomorphic_germ_multiply_commutative:commutative mul.
Proof.
move=>alpha beta.
have [f <-]:=holomorphic_germ_has_representative alpha.
have [g <-]:=holomorphic_germ_has_representative beta.
rewrite !(@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
apply:holomorphic_germ_pointwise_equality=>x;exact:mulrC.
Qed.

(** Source for [holomorphic_germ_multiply_one]: the constant-one
    germ is the multiplicative identity, 3.4.12, p. 339. *)
Lemma holomorphic_germ_multiply_one:left_id one mul.
Proof.
move=>alpha;have [f <-]:=holomorphic_germ_has_representative alpha.
rewrite /holomorphic_germ_one
  (@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
apply:holomorphic_germ_pointwise_equality=>x;exact:mul1r.
Qed.

(** Source for [holomorphic_germ_distributive]: multiplication
    distributes over addition in the ring, 3.4.12, p. 339. *)
Lemma holomorphic_germ_distributive:left_distributive mul add.
Proof.
move=>alpha beta gamma.
have [f <-]:=holomorphic_germ_has_representative alpha.
have [g <-]:=holomorphic_germ_has_representative beta.
have [h <-]:=holomorphic_germ_has_representative gamma.
rewrite !(@holomorphic_germ_add_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a))
  !(@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a))
  !(@holomorphic_germ_add_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
apply:holomorphic_germ_pointwise_equality=>x;exact:mulrDl.
Qed.

(** Source for [holomorphic_germ_one_not_zero]: the unit and zero
    are distinct in the original holomorphic ring, 3.4.12, p. 339. *)
Lemma holomorphic_germ_one_not_zero:one!=zero.
Proof.
apply/eqP=>hEqual.
have hValue:=holomorphic_germ_equal_at_centre hEqual.
change ((1:C)=0) in hValue.
by move:(oner_neq0 C);rewrite hValue eqxx.
Qed.
End RingLaws.
