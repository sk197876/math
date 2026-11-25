(** Federer (1969), 3.4.5, p. 320: zero
    germs of the original zero, unit and product obey
    exactly the printed finite-equation laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermRepresentatives AnalyticGermUP AnalyticGermSealed
  AnalyticGermRingLaws SetGermUP SetGermSealed AnalyticZeroGermUP AnalyticZeroGermSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ZeroLaws.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation zero:=(@AnalyticZeroGerm.value R X NX hNX a).
Local Notation sgerm:=(@set_germ T a).

(** Source for [analytic_zero_germ_zero]: the zero
    equation has the whole-space germ, 3.4.5, p. 320. *)
Lemma analytic_zero_germ_zero:zero (@analytic_germ_zero R X NX hNX a)=sgerm setT.
Proof.
rewrite -(@AnalyticZeroGerm.laws R X NX hNX a _
  (@analytic_constant_representative R X NX hNX a 0) (erefl _)).
congr (sgerm _);apply/seteqP;split=>x hx;first exact:Logic.I.
reflexivity.
Qed.

(** Source for [analytic_zero_germ_one]: the unit equation
    has the empty-set germ, 3.4.5, p. 320. *)
Lemma analytic_zero_germ_one:zero (@analytic_germ_one R X NX hNX a)=sgerm set0.
Proof.
rewrite -(@AnalyticZeroGerm.laws R X NX hNX a _
  (@analytic_constant_representative R X NX hNX a 1) (erefl _)).
congr (sgerm _);apply/seteqP;split=>x hx;last by case:hx.
change ((1:R)=0) in hx;by move/eqP:hx;rewrite oner_eq0.
Qed.

(** Source for [analytic_zero_germ_product]: the zero
    variety germ of a product is the union of the
    two original zero germs, 3.4.5, p. 320. *)
Lemma analytic_zero_germ_product (alpha beta:analytic_germ_space hNX a):
  zero (@AnalyticGerms.mul R X NX hNX a alpha beta)=
    @SetGerms.join T a (zero alpha) (zero beta).
Proof.
have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
have [g hg]:=@analytic_germ_has_representative R X NX hNX a beta.
have hRep:analytic_germ (@analytic_multiply_representatives R X NX hNX a f g)=
    @AnalyticGerms.mul R X NX hNX a alpha beta.
  by rewrite -hf -hg (@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
rewrite -(@AnalyticZeroGerm.laws R X NX hNX a _ _ hRep)
  -(@AnalyticZeroGerm.laws R X NX hNX a alpha f hf)
  -(@AnalyticZeroGerm.laws R X NX hNX a beta g hg)
  (@set_germ_union_equation T a _ _ _ (@SetGerms.laws T a)).
congr (sgerm _);apply/seteqP;split.
- move=>x hProduct.
  have /orP [hF|hG]:(analytic_representative_value f x==0)||(analytic_representative_value g x==0).
    by rewrite -mulf_eq0;apply/eqP;exact:hProduct.
  + left;exact:(eqP hF).
  + right;exact:(eqP hG).
- move=>x [hF|hG];change (analytic_representative_value f x*analytic_representative_value g x=0).
  + by rewrite hF mul0r.
  + by rewrite hG mulr0.
Qed.
End ZeroLaws.
