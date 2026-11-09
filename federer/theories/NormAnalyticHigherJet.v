(** Federer (1969), 3.4.5, p. 321: all fixed-order actual
    derivative fields of an analytic function are analytic, supporting
    the real Taylor coefficient proof of the cited analytic example. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearNorm
  ContinuousMultilinearSealed ContinuousMultilinearGroupingFamily NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherDifferentialLocal NormHigherDifferentialGrouping NormClassOneUP NormClassHigherDerivative
  NormRegularity NormAnalyticUP NormAnalyticLocal NormAnalyticBoundNonnegative NormSmoothFields AnalyticShiftedFactorialBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section HigherJet.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY).
Variable k:nat.
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X Y NX NY hNX hNY).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY).
Local Notation ZN:=(fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY).
Local Notation hNP:=(continuous_multilinear_norm_is_norm hNY (@ContinuousMultilinear.laws R k X Y NX NY hNX hNY)).

(** Source for [norm_analytic_higher_differential_field]: actual
    Taylor coefficient fields are analytic, supporting the example cited
    in 3.4.5, p. 321. Isometric grouping identifies every qth
    differential of the original kth field with D^(k+q)f. The
    proved fixed-shift factorial estimate supplies a finite analytic
    bound without an extra derivative regularity hypothesis. *)
Theorem norm_analytic_higher_differential_field (A:set X) (f:X->Y) (G:X->Z k):
  @norm_analytic R X Y NX NY hNX hNY A f ->
  (forall x,A x ->has_norm_higher_differential NX ev ZN A f k x (G x)) ->
  @norm_analytic R X (Z k) NX (ZN k) hNX hNP A G.
Proof.
move=>hf hG a ha.
have [U [c [hUa [hUA [hSmooth hBound]]]]]:=hf a ha.
have hc:=norm_analytic_operator_witness_nonnegative hUa hSmooth hBound.
have hZ i:is_continuous_multilinear_space NX NY (ev i) (ZN i).
  exact:ContinuousMultilinear.laws.
pose W q:=@ContinuousMultilinear.space R q X (Z k) NX (ZN k) hNX hNP.
pose ew q:=@ContinuousMultilinear.evaluation R q X (Z k) NX (ZN k) hNX hNP.
pose WN q:=@ContinuousMultilinear.norm R q X (Z k) NX (ZN k) hNX hNP.
have hW q:is_continuous_multilinear_space NX (ZN k) (ew q) (WN q).
  exact:ContinuousMultilinear.laws.
have hopen x (hx:U x):norm_domain_interior NX U x:=((hSmooth 0%N).1 x hx).1.
have hGU x (hx:U x):has_norm_higher_differential NX ev ZN U f k x (G x).
  exact:((@norm_higher_differential_open_restriction R X Y NX NY hNX hNY Z ev ZN hZ
    k A U f hUA hopen x hx (G x)).1 (hG x (hUA x hx))).
have hClass q:norm_class hNX hNP U G q.
  exact:(@norm_class_higher_derivative_field R k q X Y NX NY hNX hNY
    Z ev ZN hZ W ew WN hW U f G (hSmooth (k+q)%N) hGU).
have hRepresent x z:has_norm_higher_differential NX ev ZN U f k x z ->G x=z.
  move=>hz; have hx:=norm_higher_differential_domain hNX hz.
  exact:(norm_higher_differential_unique hNX hNY hZ (hGU x hx) hz).
have hDomain:[set x|exists z,has_norm_higher_differential NX ev ZN U f k x z]=U.
  apply/seteqP; split=>x.
  - move=>[z hz]; exact:(norm_higher_differential_domain hNX hz).
  - move=>hx; exists (G x); exact:hGU x hx.
have [J [K [hJ [hJN [hJK hKJ]]]]]:=@continuous_multilinear_grouping_family_exists R k
  X Y NX NY hNX hNY Z ev ZN hZ W ew WN hW.
have [C [hC hCb]]:=@analytic_shifted_factorial_bound_exists R c k hc.
exists U,C; split; first exact hUa.
split; first exact hUA.
split; first exact hClass.
move=>q hq x hx z hz.
have hGrouping:=@norm_higher_differential_grouping R X Y NX NY hNX Z ev ZN hZ k
  W ew WN J K hJ hJN hJK hKJ U f G hRepresent q x z.
change (has_norm_higher_differential NX ew WN
  [set y|exists v,has_norm_higher_differential NX ev ZN U f k y v] G q x z <->
  exists w:Z (k+q)%N,has_norm_higher_differential NX ev ZN U f (k+q)%N x w /\z=J q w)
  in hGrouping.
rewrite hDomain in hGrouping.
have [w [hw hEq]]:=hGrouping.1 hz.
change (is_true (WN q z<=C^+q*(q`!)%:R)).
rewrite hEq hJN.
have hPositive:(1<=k+q)%N:=leq_trans hq (leq_addl k q).
have hb:=hBound (k+q)%N hPositive x hx w hw.
have hCoefficient:c^+(k+q)*(k+q)`!%:R<=C^+q*(q`!)%:R:=hCb q hq.
exact:(le_trans hb hCoefficient).
Qed.

(** Source for [norm_analytic_higher_jet_exists]: existence of
    an actual analytic field of every fixed derivative order, supporting
    the coefficient argument for the example cited in 3.4.5, p. 321.
    Selection occurs within the existence proof; its actual derivative
    equations and analyticity are both proved. *)
Corollary norm_analytic_higher_jet_exists (A:set X) (f:X->Y):
  @norm_analytic R X Y NX NY hNX hNY A f ->
  exists G:X->Z k,
    (forall x,A x ->has_norm_higher_differential NX ev ZN A f k x (G x)) /\
    @norm_analytic R X (Z k) NX (ZN k) hNX hNP A G.
Proof.
move=>hf.
have [D hD]:=@norm_smooth_fields_exist R X Y NX NY hNX hNY A f (norm_analytic_class_all_orders hf).
exists (D k); split; first exact:(hD k).1.
exact:(norm_analytic_higher_differential_field hf (hD k).1).
Qed.
End HigherJet.
