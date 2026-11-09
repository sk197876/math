(** Federer (1969), 3.4.5, pp. 318–321: actual
    finite jets of coefficient fields. This supporting rule
    is precisely the D^q D^p identity in
    3.1.11, p. 219, on original domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  ContinuousMultilinearGroupingFamily NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherDifferentialGrouping NormFiniteJetAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section DerivativeAgreement.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable p:nat.
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X Y NX NY hNX hNY).
Local Notation ez:=(fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY).
Local Notation NZ:=(fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i X Y NX NY hNX hNY).
Local Notation hNP:=(continuous_multilinear_norm_is_norm hNY (hZ p)).
Local Notation W:=(fun i=>@ContinuousMultilinear.space R i X (Z p) NX (NZ p) hNX hNP).
Local Notation ew:=(fun i=>@ContinuousMultilinear.evaluation R i X (Z p) NX (NZ p) hNX hNP).
Local Notation NW:=(fun i=>@ContinuousMultilinear.norm R i X (Z p) NX (NZ p) hNX hNP).
Local Notation hW:=(fun i=>@ContinuousMultilinear.laws R i X (Z p) NX (NZ p) hNX hNP).

(** Source for [norm_finite_jet_derivative_agreement]:
    agreement through order p+q implies agreement through
    order q of the actual pth derivative fields,
    supporting 3.4.5, pp. 318–321. Derivative-field
    equations are required only on their original domains;
    grouping proves the conclusion without choosing coordinates. *)
Theorem norm_finite_jet_derivative_agreement (A B:X->Prop) (f g:X->Y)
    (F G:X->Z p) q a:
  (forall x,A x ->has_norm_higher_differential NX ez NZ A f p x (F x)) ->
  (forall x,B x ->has_norm_higher_differential NX ez NZ B g p x (G x)) ->
  norm_finite_jet_agreement NX ez NZ A B f g (p+q)%N a ->
  norm_finite_jet_agreement NX ew NW A B F G q a.
Proof.
move=>hF hG hAgree.
have hRepresentF x z:has_norm_higher_differential NX ez NZ A f p x z ->F x=z.
  move=>hz;have hx:=norm_higher_differential_domain hNX hz.
  exact:(norm_higher_differential_unique hNX hNY hZ (hF x hx) hz).
have hRepresentG x z:has_norm_higher_differential NX ez NZ B g p x z ->G x=z.
  move=>hz;have hx:=norm_higher_differential_domain hNX hz.
  exact:(norm_higher_differential_unique hNX hNY hZ (hG x hx) hz).
have hDomainF:[set x|exists z,has_norm_higher_differential NX ez NZ A f p x z]=A.
  apply/seteqP;split=>x.
  - move=>[z hz];exact:(norm_higher_differential_domain hNX hz).
  - move=>hx;exists (F x);exact:hF x hx.
have hDomainG:[set x|exists z,has_norm_higher_differential NX ez NZ B g p x z]=B.
  apply/seteqP;split=>x.
  - move=>[z hz];exact:(norm_higher_differential_domain hNX hz).
  - move=>hx;exists (G x);exact:hG x hx.
have [J [K [hJ [hJN [hJK hKJ]]]]]:=@continuous_multilinear_grouping_family_exists R p
  X Y NX NY hNX hNY Z ez NZ hZ W ew NW hW.
move=>i hi w.
have hGroupingF:=@norm_higher_differential_grouping R X Y NX NY hNX Z ez NZ hZ p
  W ew NW J K hJ hJN hJK hKJ A f F hRepresentF i a w.
have hGroupingG:=@norm_higher_differential_grouping R X Y NX NY hNX Z ez NZ hZ p
  W ew NW J K hJ hJN hJK hKJ B g G hRepresentG i a w.
change (has_norm_higher_differential NX ew NW
  [set x|exists z,has_norm_higher_differential NX ez NZ A f p x z] F i a w <->
  exists z:Z (p+i)%N,has_norm_higher_differential NX ez NZ A f (p+i)%N a z /\w=J i z) in hGroupingF.
change (has_norm_higher_differential NX ew NW
  [set x|exists z,has_norm_higher_differential NX ez NZ B g p x z] G i a w <->
  exists z:Z (p+i)%N,has_norm_higher_differential NX ez NZ B g (p+i)%N a z /\w=J i z) in hGroupingG.
rewrite hDomainF in hGroupingF;rewrite hDomainG in hGroupingG.
have hBound:(p+i<=p+q)%N by rewrite leq_add2l.
split=>hw.
- have [z [hz hEq]]:=hGroupingF.1 hw.
  apply:hGroupingG.2;exists z;split;last exact:hEq.
  exact:(hAgree (p+i)%N hBound z).1 hz.
- have [z [hz hEq]]:=hGroupingG.1 hw.
  apply:hGroupingF.2;exists z;split;last exact:hEq.
  exact:(hAgree (p+i)%N hBound z).2 hz.
Qed.
End DerivativeAgreement.
