(** Federer (1969), 4.1.18, pp. 375–376: the
    full-domain representative of an original-U
    Omega field has exactly the same ambient zero
    extension and the same literal support. No
    equality is replaced by almost-everywhere agreement. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain EuclideanFullDomainMeasure CompactSummableMultivectors
  CompactSummableMultivectorAmbient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section AmbientAgreement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation FT:=(current_domain R n Full).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation WU:=(@compact_summable_multivector_space R h2 n m U hU).
Local Notation WF:=(@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation valueF:=(@compact_summable_multivector_value R h2 n m Full hFull).
Local Notation rawU:=(@compact_summable_multivector_ambient_value R h2 n m U hU).
Local Notation rawF:=(@compact_summable_multivector_ambient_value R h2 n m Full hFull).

(** Source for [compact_summable_multivector_full_ambient_agreement]:
    exact ambient values of the original zero extension
    used for the two ordinary convolutions of
    Federer 4.1.18, p. 375. *)
Theorem compact_summable_multivector_full_ambient_agreement (xi:WU) (zeta:WF):
  valueF zeta=(fun x:FT=>rawU xi (set_val x))->rawF zeta=rawU xi.
Proof.
move=>hValue;apply:funext=>x.
pose x':FT:=@euclidean_full_domain_point R n x.
change (rawF zeta (set_val x')=rawU xi (set_val x')).
by rewrite compact_summable_multivector_ambient_inside hValue.
Qed.

(** Source for [compact_summable_multivector_full_support_agreement]:
    the literal support is unchanged when the original
    field is viewed on the full ambient space,
    supporting the exact K in 4.1.18, p. 375. *)
Theorem compact_summable_multivector_full_support_agreement (xi:WU) (zeta:WF):
  valueF zeta=(fun x:FT=>rawU xi (set_val x))->
  @compact_summable_multivector_ambient_support R h2 n m Full hFull zeta=
    @compact_summable_multivector_ambient_support R h2 n m U hU xi.
Proof.
move=>hValue;rewrite /compact_summable_multivector_ambient_support.
by rewrite (compact_summable_multivector_full_ambient_agreement hValue).
Qed.
End AmbientAgreement.
