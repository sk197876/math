(** Federer (1969), 3.1.24, pp. 238–239:
    a uniformly convergent homogeneous polynomial series is
    analytic. Every derivative and its bound are proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  constructive_ereal lra ring.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP NormDifferentialUP
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialUnique
  NormClassOneUP NormClassHigherUP NormRegularity NormClassInfinityPolynomial NormAffineDilationDifferentials
  SymmetricForms HomogeneousPolynomialFunctions PolynomialTaylorTerms ContinuousSymmetricFormAdapter
  NormAnalyticUP NormAnalyticCoefficientBall NormAnalyticCoefficientForms ShiftedHomogeneousDifferentials
  AnalyticCoefficientMajorant NormSmoothSeries NormOpenDomainLaws NormLinearDomainLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_polynomial_series_analytic]: implication
    (4) to (1) in Federer 3.1.24, pp. 238–239.
    Bound all coefficients on a common radius-r ball;
    polarization gives (4/r)^m m! instead of (e/r)^m m!.
    On the radius-r/16 ball the differential series have
    geometric ratio 1/2. Banach completeness and the proved
    uniform differential limit induction give all actual
    derivatives. Their geometric sums satisfy the sufficient
    analytic constant 32/r. Only the target's completeness
    is used; no additional hypothesis on the series is imposed. *)
Theorem norm_polynomial_series_analytic (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (hcomplete:is_complete_metric_space (real_norm_metric_space hNY))
    (A:set X) (f:X->Y) a :
  @norm_polynomial_analytic_at R X Y NX NY hNX hNY A f a ->
  @norm_analytic_at R X Y NX NY hNX hNY A f a.
Proof.
move=>[U [ha [hUA [P [hP hconv]]]]].
pose Z:=fun i=>@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ev:=fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose ZN:=fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ:=fun i=>@ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
have [r [hr [hBU hcoeff]]]:=@norm_analytic_coefficients_common_ball R X Y NX NY hNX hNY
  U f P a ha hP hconv.
have [phi [hphi [hphiB hphiN]]]:=@norm_analytic_coefficients_bounded_forms R X Y NX NY hNX hNY
  P r (fun m=>(hP m).1) hr hcoeff.
have hex m:=@shifted_homogeneous_differential_fields R X Y NX NY hNX hNY Z ev ZN hZ
  m (phi m) a (hphiB m).
have [E hE]:=choice hex.
pose Q m x:=sform_polynomial_value (phi m) (x-a).
pose c:=4/r.
pose s:=r/16.
pose q:=(1:R)/2.
pose W:=fun x=>NX (x-a)<s.
have hrne:r!=0:=lt0r_neq0 hr.
have hc:0<=c by apply: ltW; rewrite /c divr_gt0 // ltr0n.
have hs:0<s by rewrite /s divr_gt0 // ltr0n.
have hsr:s<r by rewrite /s; nra.
have hq:0<q<1 by rewrite /q; apply/andP; split; lra.
have hqeq:q= 2*c*s by rewrite /q /c /s; field; exact hrne.
have hWa:W a by rewrite /W subrr (real_seminorm_zero hNX.1).
have hWopen x (hx:W x):norm_domain_interior NX W x.
  exact (@norm_open_ball_domain_interior R X NX hNX a s x hx).
have hWU x (hx:W x):U x.
  have hh:=hBU (x-a) (ltW (lt_trans hx hsr)).
  by rewrite addrC subrK in hh.
have hQ m:norm_class_zero NX NY (fun _=>True) (Q m).
  have hopen x (_:True):norm_domain_interior NX (fun _=>True) x.
    exists 1; split; first exact ltr01; by move=>v hv.
  have hraw:=@norm_class_infinity_sform_polynomial R X Y NX NY hNX hNY Z ev ZN hZ
    (fun _=>True) hopen m (phi m) (hphiB m).
  have hshift:=@norm_class_infinity_affine_dilation R X Y NX NY hNX hNY Z ev ZN hZ
    (sform_polynomial_value (phi m)) 1 (-a) hraw.
  have hfun:(fun x=>sform_polynomial_value (phi m) (1*:x-a))= Q m.
    by apply: funext=>x; rewrite /Q scale1r.
  rewrite hfun in hshift; exact (hshift 0%N).1.
have hEval m i x u:@ev i u (E m i x)=
    symmetric_taylor_term i (phi m) (x-a) [tuple u j | j<i].
  exact ((hE m).1 i x u).
have hActual m i x:has_norm_higher_differential NX ev ZN (fun _=>True) (Q m) i x (E m i x).
  exact ((hE m).2.1 i x).
have hContinuous m i:norm_class_zero NX (@ZN i) (fun _=>True) (E m i).
  exact ((hE m).2.2 i).
have hzero x:@ev 0%N [ffun j:'I_0=>(0:X)] (E 0%N 0%N x)=
    sform_polynomial_value (phi 0%N) (x-a).
  exact (hActual 0%N 0%N x).2.
have [M [hM [hMp hMb]]]:=@analytic_coefficient_geometric_majorants R X Y NX NY hNX hNY Z ev ZN hZ
  phi E W a c s q hc (ltW hs) hq hqeq (fun x hx=>ltW hx) hphiN hEval hzero.
have hSum N x:(\sum_(m<N) Q m x)= \sum_(m<N) P m (x-a).
  apply: eq_bigr=>m _; symmetry; exact (hphi m (x-a)).
have hFconv eps (he:0<eps):exists n:nat,forall N,(n<=N)%N -> forall x,W x ->
    NY ((\sum_(m<N) Q m x)-f x)<eps.
  have [n hn]:=hconv eps he.
  exists n.+1; move=>[|N] hN; first by [].
  move=>x hx.
  have hnN:(n<=N)%N:=hN.
  rewrite hSum (real_seminorm_subtract hNY.1).
  exact (hn N hnN x (hWU x hx)).
have [G [hclass [hactual hbound]]]:=@norm_geometrically_dominated_smooth_series R X Y NX NY hNX hNY
  hcomplete Z ev ZN hZ W Q E f q M (@norm_open_ball_convex R X NX hNX a s)
  hWopen hq hM hQ hActual hContinuous hMb hFconv.
pose C:=2*(2*c/q).
exists W,C; split; first exact hWa.
split; first by move=>x hx; exact (hUA x (hWU x hx)).
split; first exact hclass.
move=>i hi x hx z hz.
have hzg:z= G i x:=@norm_higher_differential_unique R X Y NX NY hNX hNY Z ev ZN hZ
  W f i x z (G i x) hz (hactual i x hx).
rewrite hzg.
have hh:=hbound i x hx; rewrite (hMp i hi) in hh.
have hden:(1-q)^-1= 2 by rewrite /q; field.
rewrite hden in hh.
apply: le_trans hh _.
have htwo:(2:R)<=2^+i:=ler_eXnr hi (ler1n R 2).
have hn:0<=(2*c/q)^+i*(i`!)%:R by rewrite -(hMp i hi); exact (hM i).
have hprod:=ler_wpM2r hn htwo.
have heq:C^+i*(i`!)%:R= 2^+i*((2*c/q)^+i*(i`!)%:R) by rewrite /C exprMn; ring.
rewrite heq [((2*c/q)^+i*(i`!)%:R)*2]mulrC.
exact hprod.
Qed.
