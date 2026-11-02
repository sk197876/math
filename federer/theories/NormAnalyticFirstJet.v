(** Federer (1969), 3.2.33, p. 270: actual
    differentials of analytic functions are analytic, supporting
    the analytic exterior rank tests. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearNorm
  ContinuousMultilinearSealed ContinuousMultilinearGroupingFamily NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherDifferentialLocal NormHigherDifferentialGrouping NormClassOneUP NormClassHigherDerivative
  NormRegularity NormAnalyticUP NormAnalyticLocal NormAnalyticBoundNonnegative NormSmoothFields AnalyticSuccessorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FirstJet.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY).
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X Y NX NY hNX hNY).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY).
Local Notation ZN:=(fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY).
Local Notation hNP:=(continuous_multilinear_norm_is_norm hNY (@ContinuousMultilinear.laws R 1%N X Y NX NY hNX hNY)).

(** Source for [norm_analytic_first_higher_differential]:
    the analytic h_i built from Df in Federer 3.2.33,
    p. 270, use closure of analyticity under differentiation.
    The actual derivative-field theorem and isometric grouping
    identify D^q(Df) with D^(q+1)f on the same open domain.
    The factorial estimate is absorbed in one finite constant
    at every positive order. No analytic derivative or formal
    power-series manipulation is assumed in the conclusion. *)
Theorem norm_analytic_first_higher_differential (A:set X) (f:X->Y) (G:X->Z 1%N):
  @norm_analytic R X Y NX NY hNX hNY A f ->
  (forall x,A x ->has_norm_higher_differential NX ev ZN A f 1%N x (G x)) ->
  @norm_analytic R X (Z 1%N) NX (ZN 1%N) hNX hNP A G.
Proof.
move=>hf hG a ha.
have [U [c [hUa [hUA [hSmooth hBound]]]]]:=hf a ha.
have hc:=norm_analytic_operator_witness_nonnegative hUa hSmooth hBound.
have hZ i:is_continuous_multilinear_space NX NY (ev i) (ZN i).
  exact:ContinuousMultilinear.laws.
pose W q:=@ContinuousMultilinear.space R q X (Z 1%N) NX (ZN 1%N) hNX hNP.
pose ew q:=@ContinuousMultilinear.evaluation R q X (Z 1%N) NX (ZN 1%N) hNX hNP.
pose WN q:=@ContinuousMultilinear.norm R q X (Z 1%N) NX (ZN 1%N) hNX hNP.
have hW q:is_continuous_multilinear_space NX (ZN 1%N) (ew q) (WN q).
  exact:ContinuousMultilinear.laws.
have hopen x (hx:U x):norm_domain_interior NX U x:=((hSmooth 0%N).1 x hx).1.
have hGU x (hx:U x):has_norm_higher_differential NX ev ZN U f 1%N x (G x).
  exact:((@norm_higher_differential_open_restriction R X Y NX NY hNX hNY Z ev ZN hZ
    1%N A U f hUA hopen x hx (G x)).1 (hG x (hUA x hx))).
have hClass q:norm_class hNX hNP U G q.
  exact:(@norm_class_higher_derivative_field R 1%N q X Y NX NY hNX hNY
    Z ev ZN hZ W ew WN hW U f G (hSmooth (1+q)%N) hGU).
have hRepresent x z:has_norm_higher_differential NX ev ZN U f 1%N x z ->G x=z.
  move=>hz; have hx:=norm_higher_differential_domain hNX hz.
  exact:(norm_higher_differential_unique hNX hNY hZ (hGU x hx) hz).
have hDomain:[set x|exists z,has_norm_higher_differential NX ev ZN U f 1%N x z]=U.
  apply/seteqP; split=>x.
  - move=>[z hz]; exact:(norm_higher_differential_domain hNX hz).
  - move=>hx; exists (G x); exact:hGU x hx.
have [J [K [hJ [hJN [hJK hKJ]]]]]:=@continuous_multilinear_grouping_family_exists R 1%N
  X Y NX NY hNX hNY Z ev ZN hZ W ew WN hW.
exists U,((c+1)*(2*c)); split; first exact hUa.
split; first exact hUA.
split; first exact hClass.
move=>q hq x hx z hz.
have hGrouping:=@norm_higher_differential_grouping R X Y NX NY hNX Z ev ZN hZ 1%N
  W ew WN J K hJ hJN hJK hKJ U f G hRepresent q x z.
change (has_norm_higher_differential NX ew WN
  [set y|exists v,has_norm_higher_differential NX ev ZN U f 1%N y v] G q x z <->
  exists w:Z (1+q)%N,has_norm_higher_differential NX ev ZN U f (1+q)%N x w /\z=J q w)
  in hGrouping.
rewrite hDomain in hGrouping.
have [w [hw hEq]]:=hGrouping.1 hz.
change (is_true (WN q z<=((c+1)*(2*c))^+q*(q`!)%:R)).
rewrite hEq hJN.
have hPositive:(1<=1+q)%N by rewrite leq_addr.
have hb:=hBound (1+q)%N hPositive x hx w hw.
have hCoefficient:c^+(1+q)*(1+q)`!%:R<=((c+1)*(2*c))^+q*(q`!)%:R.
  rewrite add1n; exact:(analytic_successor_factorial_bound hc hq).
exact:(le_trans hb hCoefficient).
Qed.

(** Source for [norm_analytic_first_jet_exists]: supporting the
    actual analytic rank tests in Federer 3.2.33, p. 270.
    Analyticity supplies a smooth actual jet field. The preceding
    theorem proves that same first jet analytic, so the final
    rank argument need not assume any chosen derivative field. *)
Corollary norm_analytic_first_jet_exists (A:set X) (f:X->Y):
  @norm_analytic R X Y NX NY hNX hNY A f ->
  exists G:X->Z 1%N,
    (forall x,A x ->has_norm_higher_differential NX ev ZN A f 1%N x (G x)) /\
    @norm_analytic R X (Z 1%N) NX (ZN 1%N) hNX hNP A G.
Proof.
move=>hf.
have [D hD]:=@norm_smooth_fields_exist R X Y NX NY hNX hNY A f (norm_analytic_class_all_orders hf).
exists (D 1%N); split; first exact:(hD 1%N).1.
exact:(norm_analytic_first_higher_differential hf (hD 1%N).1).
Qed.
End FirstJet.
