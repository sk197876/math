(** Federer (1969), 3.4.6, pp. 322–323: actual
    iterated divided directional coefficients equal the original
    mixed divided derivative. Grouping is the proved identity
    of 3.1.11, p. 219. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets ring.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormDifferentialLinear
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm ContinuousMultilinearEvaluationBound
  ContinuousMultilinearGroupingFamily ContinuousMultilinearPostcompose MultilinearArguments
  NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherDifferentialGrouping NormHigherDifferentialPostcompose
  NormHigherDifferentialLocal NormAnalyticUP NormAnalyticLocal NormAnalyticHigherJet NormSmoothFields
  AnalyticDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Mixed.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X R^o NX N hNX hN).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN).
Local Notation NZ:=(fun i=>@ContinuousMultilinear.norm R i X R^o NX N hNX hN).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i X R^o NX N hNX hN).
Local Notation AN A f:=(@norm_analytic R X R^o NX N hNX hN A f).
Local Notation Coefficient:=(@is_analytic_directional_coefficient R X R^o NX N hNX hN).

(** Source for [weierstrass_iterated_coefficient_value]: the
    actual divided v-derivative followed by the divided
    w-derivative is D^(i+j) evaluated on the original
    two argument blocks and divided by i!j!,
    3.4.6, pp. 322–323. No independent mixed
    coefficient or derivative-field identity is assumed. *)
Theorem weierstrass_iterated_coefficient_value (A:set X) (f:X->R) a v w i j (C P:X->R)
    (z:Z (i+j)%N):
  A a ->AN A f ->Coefficient A f i v C ->Coefficient A C j w P ->
  has_norm_higher_differential NX ev NZ A f (i+j)%N a z ->
  P a=((i`!)%:R*(j`!)%:R)^-1*
    ev (i+j)%N (multilinear_arguments_join [ffun _:'I_i=>v] [ffun _:'I_j=>w]) z.
Proof.
move=>ha hf hC hP hz.
have hOpen x (hx:A x):norm_domain_interior NX A x:=
  ((norm_analytic_class_all_orders hf 0%N).1 x hx).1.
have [G [hG hAnalyticG]]:=@norm_analytic_higher_jet_exists R X R^o NX N hNX hN i A f hf.
have [D hD]:=@norm_smooth_fields_exist R X R^o NX N hNX hN A f (norm_analytic_class_all_orders hf).
pose hNP:=continuous_multilinear_norm_is_norm hN (hZ i).
pose W q:=@ContinuousMultilinear.space R q X (Z i) NX (NZ i) hNX hNP.
pose ew q:=@ContinuousMultilinear.evaluation R q X (Z i) NX (NZ i) hNX hNP.
pose NW q:=@ContinuousMultilinear.norm R q X (Z i) NX (NZ i) hNX hNP.
pose hW q:=@ContinuousMultilinear.laws R q X (Z i) NX (NZ i) hNX hNP.
have [J [K [hJ [hJN [hJK hKJ]]]]]:=@continuous_multilinear_grouping_family_exists R i
  X R^o NX N hNX hN Z ev NZ hZ W ew NW hW.
have hRepresent x y:has_norm_higher_differential NX ev NZ A f i x y ->G x=y.
  move=>hy;have hx:=norm_higher_differential_domain hNX hy.
  exact:(norm_higher_differential_unique hNX hN hZ (hG x hx) hy).
have hDomain:[set x|exists y,has_norm_higher_differential NX ev NZ A f i x y]=A.
  apply/seteqP;split=>x.
  - move=>[y hy].
    have hx:=norm_higher_differential_domain hNX hy.
    exact:hx.
  - move=>hx;exists (G x);exact:hG x hx.
have hGrouped x (hx:A x):has_norm_higher_differential NX ew NW A G j x (J j (D (i+j)%N x)).
  have hGrouping:=@norm_higher_differential_grouping R X R^o NX N hNX Z ev NZ hZ i
    W ew NW J K hJ hJN hJK hKJ A f G hRepresent j x (J j (D (i+j)%N x)).
  change (has_norm_higher_differential NX ew NW
    [set t|exists y,has_norm_higher_differential NX ev NZ A f i t y] G j x (J j (D (i+j)%N x))<->
    exists y:Z (i+j)%N,has_norm_higher_differential NX ev NZ A f (i+j)%N x y /\
      J j (D (i+j)%N x)=J j y) in hGrouping.
  rewrite hDomain in hGrouping;apply:hGrouping.2.
  exists (D (i+j)%N x);split;first exact:(hD (i+j)%N).1 x hx.
  reflexivity.
pose L:Hom (Z i) R^o:=((i`!)%:R)^-1*:(ev i [ffun _:'I_i=>v]).
have hEvalBound:norm_bounded_linear (NZ i) N (ev i [ffun _:'I_i=>v]).
  exact:(@continuous_multilinear_evaluation_bounded R i X R^o (Z i) NX N hNX
    (ev i) (NZ i) (hZ i) [ffun _: 'I_i=>v]).
have hL:norm_bounded_linear (NZ i) N L:=norm_bounded_linear_scale hN _ hEvalBound.
have [M [hM hMBounded]]:=@continuous_multilinear_postcompose_family_exists R X (Z i) R^o
  NX (NZ i) N W Z ew NW ev NZ hW hZ L hL.
have hActual:=@norm_higher_differential_field_postcompose R X (Z i) R^o NX (NZ i) N
  hNX hNP hN W Z ew NW ev NZ hW hZ L M hM hMBounded A G j
  (fun x=>J j (D (i+j)%N x)) hGrouped a ha.
have hValue x (hx:A x):C x=L (G x).
  by rewrite (hC x hx (G x) (hG x hx)) /L hom_scaleE.
have hActualC:has_norm_higher_differential NX ev NZ A C j a (M j (J j (D (i+j)%N a))).
  exact:((@norm_higher_differential_local_agreement R X R^o NX N hNX hN Z ev NZ hZ
    j A A A (fun x=>L (G x)) C hOpen (fun x _=>iff_refl _)
    (fun x hx _=>esym (hValue x hx)) a ha _).1 hActual).
have hDValue:D (i+j)%N a=z:=norm_higher_differential_unique hNX hN hZ ((hD (i+j)%N).1 a ha) hz.
rewrite (hP a ha _ hActualC) hM /L hom_scaleE hJ hDValue.
change (((j`!)%:R:R)^-1*(((i`!)%:R:R)^-1*
    ev (i+j)%N (multilinear_arguments_join [ffun _:'I_i=>v] [ffun _:'I_j=>w]) z)=
  (((i`!)%:R:R)*(j`!)%:R)^-1*
    ev (i+j)%N (multilinear_arguments_join [ffun _:'I_i=>v] [ffun _:'I_j=>w]) z).
rewrite invfM;ring.
Qed.
End Mixed.
