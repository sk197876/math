(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 320: zero
    germs of the original zero, unit and product obey
    exactly the printed finite-equation laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermSealed
  HolomorphicGermRingLaws SetGermUP SetGermSealed HolomorphicZeroGermUP HolomorphicZeroGermSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ZeroLaws.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation zero:=(@HolomorphicZeroGerm.value R X NX hNX a).
Local Notation sgerm:=(@set_germ T a).

(** Source for [holomorphic_zero_germ_zero]: the zero
    equation has the whole-space germ, 3.4.5, p. 320. *)
Lemma holomorphic_zero_germ_zero:zero (@holomorphic_germ_zero R X NX hNX a)=sgerm setT.
Proof.
rewrite -(@HolomorphicZeroGerm.laws R X NX hNX a _
  (@holomorphic_constant_representative R X NX hNX a 0) (erefl _)).
congr (sgerm _);apply/seteqP;split=>x hx;first exact:Logic.I.
reflexivity.
Qed.

(** Source for [holomorphic_zero_germ_one]: the unit equation
    has the empty-set germ, 3.4.5, p. 320. *)
Lemma holomorphic_zero_germ_one:zero (@holomorphic_germ_one R X NX hNX a)=sgerm set0.
Proof.
rewrite -(@HolomorphicZeroGerm.laws R X NX hNX a _
  (@holomorphic_constant_representative R X NX hNX a 1) (erefl _)).
congr (sgerm _);apply/seteqP;split=>x hx;last by case:hx.
change ((1:ComplexScalars.C R)=0) in hx;by move/eqP:hx;rewrite oner_eq0.
Qed.

(** Source for [holomorphic_zero_germ_product]: the zero
    variety germ of a product is the union of the
    two original zero germs, 3.4.5, p. 320. *)
Lemma holomorphic_zero_germ_product (alpha beta:holomorphic_germ_space hNX a):
  zero (@HolomorphicGerms.mul R X NX hNX a alpha beta)=
    @SetGerms.join T a (zero alpha) (zero beta).
Proof.
have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
have [g hg]:=@holomorphic_germ_has_representative R X NX hNX a beta.
have hRep:holomorphic_germ (@holomorphic_multiply_representatives R X NX hNX a f g)=
    @HolomorphicGerms.mul R X NX hNX a alpha beta.
  by rewrite -hf -hg (@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
rewrite -(@HolomorphicZeroGerm.laws R X NX hNX a _ _ hRep)
  -(@HolomorphicZeroGerm.laws R X NX hNX a alpha f hf)
  -(@HolomorphicZeroGerm.laws R X NX hNX a beta g hg)
  (@set_germ_union_equation T a _ _ _ (@SetGerms.laws T a)).
congr (sgerm _);apply/seteqP;split.
- move=>x hProduct.
  have /orP [hF|hG]:(holomorphic_representative_value f x==0)||(holomorphic_representative_value g x==0).
    by rewrite -mulf_eq0;apply/eqP;exact:hProduct.
  + left;exact:(eqP hF).
  + right;exact:(eqP hG).
- move=>x [hF|hG];change (holomorphic_representative_value f x*holomorphic_representative_value g x=0).
  + by rewrite hF mul0r.
  + by rewrite hG mulr0.
Qed.
End ZeroLaws.
