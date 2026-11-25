(** Federer (1969), 3.4.7, p. 325: the actual
    germ value is a ring homomorphism. Local representative
    choice serves only to prove existence; centre equality
    makes the value independent of that choice. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermSealed AnalyticGermRingLaws AnalyticGermRing AnalyticGermValueUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Existence.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].

(** Source for [analytic_germ_value_witness]: the value
    of a local representative is a private existence
    witness, supporting 3.4.7, p. 325. *)
Definition analytic_germ_value_witness (alpha:G):R:=
  analytic_representative_value
    (projT1 (cid (@analytic_germ_has_representative R X NX hNX a alpha))) a.

(** Source for [analytic_germ_value_witness_representative]: every
    original representative gives the same centre value,
    supporting the independent laws in 3.4.7, p. 325. *)
Lemma analytic_germ_value_witness_representative (f:@analytic_representative_type R X NX hNX a):
  analytic_germ_value_witness (analytic_germ f) = analytic_representative_value f a.
Proof.
have hEqual:=projT2 (cid (@analytic_germ_has_representative R X NX hNX a (analytic_germ f))).
exact:(@analytic_germ_equal_at_centre R X NX hNX a _ f hEqual).
Qed.

(** Source for [analytic_germ_value_additive]: centre values
    preserve addition and zero, supporting the specialization
    in 3.4.7, p. 325. *)
Lemma analytic_germ_value_additive:nmod_morphism analytic_germ_value_witness.
Proof.
split.
- exact:(analytic_germ_value_witness_representative (@analytic_constant_representative R X NX hNX a 0)).
- move=>alpha beta.
  have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
  have [g hg]:=@analytic_germ_has_representative R X NX hNX a beta.
  rewrite -hf -hg.
  change (analytic_germ_value_witness (@AnalyticGerms.add R X NX hNX a (analytic_germ f) (analytic_germ g)) =
    analytic_germ_value_witness (analytic_germ f)+analytic_germ_value_witness (analytic_germ g)).
  rewrite (@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
  by rewrite !analytic_germ_value_witness_representative.
Qed.
#[local] HB.instance Definition _:=GRing.isNmodMorphism.Build G R
  analytic_germ_value_witness analytic_germ_value_additive.

(** Source for [analytic_germ_value_multiplicative]: centre
    values preserve products and one, supporting units
    and specialization in 3.4.7, p. 325. *)
Lemma analytic_germ_value_multiplicative:monoid_morphism analytic_germ_value_witness.
Proof.
split.
- exact:(analytic_germ_value_witness_representative (@analytic_constant_representative R X NX hNX a 1)).
- move=>alpha beta.
  have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
  have [g hg]:=@analytic_germ_has_representative R X NX hNX a beta.
  rewrite -hf -hg.
  change (analytic_germ_value_witness (@AnalyticGerms.mul R X NX hNX a (analytic_germ f) (analytic_germ g)) =
    analytic_germ_value_witness (analytic_germ f)*analytic_germ_value_witness (analytic_germ g)).
  rewrite (@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
  by rewrite !analytic_germ_value_witness_representative.
Qed.
#[local] HB.instance Definition _:=GRing.isMonoidMorphism.Build G R
  analytic_germ_value_witness analytic_germ_value_multiplicative.

(** Source for [analytic_germ_value_exists]: an actual
    representative-independent centre-value homomorphism exists,
    supporting the original argument in 3.4.7, p. 325. *)
Theorem analytic_germ_value_exists:
  exists value:{rmorphism G->R},is_analytic_germ_value_at_centre value.
Proof.
exists (GRing.RMorphism.clone G R analytic_germ_value_witness _).
exact:analytic_germ_value_witness_representative.
Qed.
End Existence.
