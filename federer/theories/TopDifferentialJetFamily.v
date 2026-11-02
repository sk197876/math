(** Federer (1969), 3.1.15, pp. 227–228:
    "We will show that the hypotheses of 3.1.14 hold with Y, k, A
    replaced by R^n, k+1, F." The (k+1)-jets P_a of f at the points
    of the closed set F, on which D^k f is differentiable with the
    continuous derivative T at uniform rates on bounded sets, form a
    Whitney jet family of order k+1: for a compact C in F the
    quotients defining rho(C,delta) are controlled, for i<k by the
    refined remainder estimate, for i=k by the rate of D^k f, and
    for i=k+1 by the uniform continuity of D^(k+1) f on C. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  finmap reals constructive_ereal topology lra.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness RealNormUP
  SymmetricForms PolynomialFunctions PolynomialRepresentations PolynomialTaylor
  ContinuousMultilinearUP ContinuousMultilinearNorm NormDifferentialUP NormClassOneUP
  NormHigherDifferentialUP NormHigherDifferentialUnique NormClassHigherUP
  NormJetUP NormJet MultilinearSuccessorArguments WhitneyModulusUP WhitneyFormBridge
  ExtendedSupremumUP CompactNormDomainRadius CompactNearbyUniformContinuity NormMetric
  CompactFiniteCover MetricClosedBalls ArchimedeanReciprocal
  TopDifferentialLowOrderEstimate JetTopDifferentialLaws SuccessorLiftDifferenceBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Section JetFamily.
Variable R : realType.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) (R_n R n).
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space N NY (@ev i) (@ZN i).
Variable k : nat.
Variable B : set X.
Variable f : X->R_n R n.
Hypothesis hf : norm_class_higher N NY ev ZN B f k.
Variable Dk : X->Z k.
Hypothesis hDkf : forall x, B x -> has_norm_higher_differential N ev ZN B f k x (Dk x).
Variable F : set X.
Hypothesis hFc : closed F.
Hypothesis hFB : F `<=` B.
Variable T : X->Hom X (Z k).
Hypothesis hFdiff : forall a, F a -> has_norm_differential N (@ZN k) B Dk a (T a).
Hypothesis hFcont : forall a, F a -> forall t : R, 0<t -> exists d : R, 0<d /\
  forall b, F b -> N (b-a)<d -> forall h, @ZN k ((T b-T a) h)<=t*N h.
Hypothesis hFrate : forall (rho : R) (j : nat), exists Q : nat, forall a, F a -> N a<=rho ->
  forall x, B x -> 0<N (x-a) -> N (x-a)<(Q.+1%:R)^-1 ->
  @ZN k (Dk x-Dk a-T a (x-a))<=(j.+1%:R)^-1*N (x-a).
Variable zz : X->Z k.+1.
Hypothesis hzz : forall a, F a -> has_norm_higher_differential N ev ZN B f k.+1 a (zz a).
Hypothesis hlift : forall a, F a -> forall u v,
  @ev k u (T a v)=@ev k.+1 (multilinear_successor_arguments u v) (zz a).
Variable P : X->PolynomialFunction (R_n R m) (R_n R n).
Hypothesis hP : forall a, F a -> is_norm_jet_polynomial N ev ZN B f k.+1 a (P a).
Let hZNk : is_real_norm (@ZN k) := continuous_multilinear_norm_is_norm hNY (@hZ k).
Let hZNk1 : is_real_norm (@ZN k.+1) := continuous_multilinear_norm_is_norm hNY (@hZ k.+1).

(** Source for [compact_norm_bounded]:
    a compact subset of R^m is bounded, Federer 2.2.5, p. 62:
    the open balls about the origin of integer radius cover it
    and a finite subfamily suffices. *)
Lemma compact_norm_bounded (C : set X) : compact C -> exists rho : R, forall x, C x -> N x<=rho.
Proof.
move=>hC.
pose U (j : nat) : set X := [set x | mdist (0:X) x<j%:R].
have hUo : forall j, [set: nat] j -> open (U j) by move=>j _; exact: metric_open_ball_open.
have hcov : C `<=` \bigcup_(j in [set: nat]) U j.
  move=>x _; have /andP [_ hx] := truncn_itv (mdist_ge0 (0:X) x).
  by exists (Num.truncn (mdist (0:X) x)).+1=>//; rewrite /U /=.
have [D' hD' hCD'] := compact_open_finite_cover hC hUo hcov.
exists ((\max_(j <- enum_fset D') j)%:R)=>x hx.
have [j hj hxj] := hCD' x hx.
have hNx : mdist (0:X) x=N x by rewrite inner_metric_distanceE sub0r inner_normN.
rewrite -hNx; apply: ltW (lt_le_trans hxj _); rewrite ler_nat.
exact: (@leq_bigmax_seq _ (enum_fset D') xpredT (fun i=>i) j hj isT).
Qed.

(** Source for [compact_segment_radius]:
    a compact subset of the open set B has a uniform radius
    of balls inside B, Federer 2.2.5, p. 62, used for the
    segments of the Taylor formulae in 3.1.15, p. 228. *)
Lemma compact_segment_radius (C : set X) : C `<=` B -> compact C ->
  exists d : R, 0<d /\ forall a h, C a -> N h<d -> B (a+h).
Proof.
move=>hCB hC.
have hpt : forall c : X, C c -> exists r : R, 0<r /\ forall y : X, mdist c y<r -> B y.
  move=>c hc.
  have [r [hr hball]] := (hf.1 c (hCB c hc)).1.
  exists r; split=>// y hy.
  have -> : y=c+(y-c) by rewrite addrCA subrr addr0.
  apply: hball; rewrite -(real_seminorm_subtract hN.1) -inner_metric_distanceE; exact: hy.
have [d [hd hunif]] := metric_compact_uniform_domain_radius hC hpt.
exists d; split=>// a h ha hh.
apply: (hunif a (a+h) ha).
by rewrite inner_metric_distanceE opprD addrA subrr sub0r inner_normN.
Qed.

(** Source for [top_jet_uniform]:
    "D^(k+1) f is uniformly continuous on C", Federer 3.1.15,
    p. 228: the operator continuity of T on F gives the
    continuity of the lifted top differentials, uniform on
    compact subsets of F by 2.2.7, p. 64. *)
Lemma top_jet_uniform (C : set X) : C `<=` F -> compact C -> forall e : R, 0<e ->
  exists d : R, 0<d /\ forall a b, C a -> C b -> N (b-a)<d -> @ZN k.+1 (zz b-zz a)<=e.
Proof.
move=>hCF hC e he.
have hpt : forall c : X, C c -> forall t : R, 0<t -> exists r : R, 0<r /\
    forall y : X, F y -> mdist c y<r ->
    mdist (zz c : real_norm_metric_space hZNk1) (zz y : real_norm_metric_space hZNk1)<t.
  move=>c hc t ht.
  have ht2 : 0<t/2 by exact: divr_gt0.
  have [r [hr hcont]] := hFcont (hCF c hc) ht2.
  exists r; split=>// y hy hcy.
  rewrite real_norm_metric_distanceE.
  have hyc : N (y-c)<r by rewrite (real_seminorm_subtract hN.1) -inner_metric_distanceE.
  have hb : forall v, @ZN k ((T y-T c) v)<=(t/2)*N v := hcont y hy hyc.
  have hle := successor_lift_difference_bound hN hZ (hlift (hCF c hc)) (hlift hy) (ltW ht2) hb.
  rewrite (real_seminorm_subtract hZNk1.1); apply: (le_lt_trans hle); lra.
have [d [hd hunif]] := metric_compact_uniform_nearby (f:=zz : X->real_norm_metric_space hZNk1)
  hC hCF hpt he.
exists d; split=>// a b ha hb hba.
have hab : mdist a b<d by rewrite inner_metric_distanceE (real_seminorm_subtract hN.1).
have := hunif a b ha (hCF b hb) hab.
rewrite real_norm_metric_distanceE (real_seminorm_subtract hZNk1.1)=>h; exact: ltW h.
Qed.

(** Source for [top_differential_jet_family]:
    the hypotheses of Whitney's extension theorem hold for the
    (k+1)-jets on F, Federer 3.1.15, pp. 227–228: F is closed,
    the jets have degree at most k+1, and rho(C,delta) tends to
    zero on compact subsets C of F by the three estimates of
    p. 228. *)
Theorem top_differential_jet_family : is_whitney_jet_family NY k.+1 P F.
Proof.
split; first exact: hFc.
split; first by move=>a ha; exact: (norm_jet_polynomial_degree (hP ha)).
move=>C hCF hC e he.
have hCB : C `<=` B := subset_trans hCF hFB.
have [rho hrho] := compact_norm_bounded hC.
have [DP [hDPe hDPd]] := whitney_polynomial_fields_exist hNY hZ.
have hbase : forall c, F c -> forall i, (i<=k.+1)%N ->
    has_norm_higher_differential N ev ZN B f i c (DP (P c) i c).
  move=>c hc i hi.
  have [E [hE _]] := norm_jet_polynomial_expansion (hP hc).
  have hat := norm_jet_differential_at_base hN hNY hZ (hP hc) hi (hE i hi).
  by rewrite (norm_higher_differential_unique hN hNY hZ (hDPd (P c) i c) hat); exact: hE.
have hk2 : (0:R)<k.+2%:R by rewrite ltr0n.
have he' : 0<e/k.+2%:R by exact: divr_gt0.
have [j hj] := real_reciprocal_below he'.
set eta : R := (j.+1%:R)^-1.
have heta0 : 0<=eta by rewrite invr_ge0 ler0n.
have heta_e : eta*k.+2%:R<e by rewrite -(ltr_pdivlMr _ _ hk2).
have heta_lt : eta<e.
  apply: (le_lt_trans _ heta_e); rewrite -[eta in X in X<=_]mulr1.
  by apply: (ler_wpM2l heta0); rewrite ler1n.
have [Q hQ] := hFrate rho j.
set r : R := (Q.+1%:R)^-1.
have hr : 0<r by rewrite invr_gt0 ltr0n.
have hrateA : forall a, C a -> forall x, B x -> N (x-a)<r ->
    @ZN k (Dk x-Dk a-T a (x-a))<=eta*N (x-a).
  move=>a ha x hx hxr.
  have hN0 := real_seminorm_nonnegative hN.1 (x-a).
  rewrite le_eqVlt in hN0; case/orP: hN0=>[/eqP h0|hpos].
  - have hz : x-a=0 by apply: hN.2; rewrite -h0.
    have hxa : x=a by rewrite -(subrK a x) hz add0r.
    rewrite hxa !subrr raddf0 subr0 (real_seminorm_zero hZNk.1) (real_seminorm_zero hN.1) mulr0.
    exact: lexx.
  - exact: (hQ a (hCF a ha) (hrho a ha) x hx hpos hxr).
have [d1 [hd1 hseg]] := compact_segment_radius hCB hC.
have [d2 [hd2 hunif]] := top_jet_uniform hCF hC he.
set delta := Num.min (Num.min r d1) d2/2.
have hdelta : 0<delta by rewrite /delta divr_gt0 // !lt_min hr hd1 hd2.
have hm1 : Num.min (Num.min r d1) d2<=r by rewrite ge_min ge_min lexx.
have hm2 : Num.min (Num.min r d1) d2<=d1 by rewrite ge_min ge_min lexx orbT.
have hm3 : Num.min (Num.min r d1) d2<=d2 by rewrite ge_min lexx orbT.
have hdr : delta<r by rewrite /delta; lra.
have hdd1 : delta<d1 by rewrite /delta; lra.
have hdd2 : delta<d2 by rewrite /delta; lra.
exists delta; split=>// d hd0 hdd.
apply: (extended_supremum_least (whitney_modulusP NY k.+1 P C d)).
move=>x [[i [a [b [q [hi [ha [hb [hp [hdab [hq hx]]]]]]]]]]|->]; last by rewrite lee_fin ltW.
rewrite hx lee_fin.
have haF : F a := hCF a ha.
have hbF : F b := hCF b hb.
have hab : N (a-b)=N (b-a) := real_seminorm_subtract hN.1 a b.
have hba_small : N (b-a)<=delta by rewrite -hab; exact: (le_trans hdab hdd).
have hbr : N (b-a)<r := le_lt_trans hba_small hdr.
have hseg' : forall t : R, 0<=t<= 1 -> B (a+t*:(b-a)).
  move=>t /andP [ht0 ht1]; apply: (hseg a _ ha).
  rewrite (real_seminorm_scale hN.1) (ger0_norm ht0).
  apply: (le_lt_trans (ler_piMl (real_seminorm_nonnegative hN.1 _) ht1)).
  exact: (le_lt_trans hba_small hdd1).
have hqE : q=@ZN i (DP (P a) i b-DP (P b) i b).
  apply: EFin_inj; rewrite -hq /whitney_difference_norm.
  exact: (whitney_coefficient_difference_norm hNY hZ hDPe (P a) (P b) i b).
have hA0 : 0<(N (a-b))^+(k.+1-i)%N := exprn_gt0 _ hp.
have hF0 : 0<(((k.+1-i)%N)`!)%:R :> R by rewrite ltr0n fact_gt0.
suff hkey : q<=e*(N (a-b))^+(k.+1-i)%N/(((k.+1-i)%N)`!)%:R.
  by rewrite -(ler_pdivlMr _ _ hF0) (ler_pdivrMr _ _ hA0) mulrAC.
rewrite hqE.
case: (ltngtP i k)=>[hik|hik|hik].
- (* i<k: the refined remainder *)
  have hK : k=(i+(k-i.+1).+1)%N by rewrite subnSK // subnKC // ltnW.
  have hlow := low_order_estimate hNY hZ hK hf hDkf (hFdiff haF) (hzz haF) (hlift haF)
    heta0 hr (hrateA a ha) (hP haF) hbr hseg' (hDPd (P a) i b) (hbase b hbF i hi).
  apply: (le_trans hlow).
  have hn : (k-i.+1).+2=(k.+1-i)%N by rewrite subnSK // subSn // ltnW.
  have hfact : ((k-i.+1).+1)`!=((k-i)`!)%N by rewrite subnSK.
  have hfact' : ((k.+1-i)%N)`!=((k-i).+1*(k-i)`!)%N by rewrite subSn ?factS // ltnW.
  rewrite hn hfact hfact' natrM -hab.
  set A' := (N (a-b))^+(k.+1-i)%N.
  set c := ((k-i)`!)%:R : R.
  set s := ((k-i).+1)%:R : R.
  have hA' : 0<=A' := ltW hA0.
  have hc : 0<c by rewrite ltr0n fact_gt0.
  have hs : 0<s by rewrite ltr0n.
  have -> : e*A'/(s*c)=(e/s)*A'/c by rewrite invfM mulrA [e*A'*s^-1]mulrAC.
  apply: ler_wpM2r; first by rewrite invr_ge0 ltW.
  apply: (ler_wpM2r hA').
  rewrite ler_pdivlMr //; apply: (le_trans _ (ltW heta_e)); apply: (ler_wpM2l heta0).
  by rewrite /s ler_nat ltnS; exact: (leq_trans (leq_subr _ _) (leqnSn _)).
- (* i=k+1: the uniform continuity of the top differential *)
  have hik1 : i=k.+1 by apply/eqP; rewrite eqn_leq hi hik.
  subst i.
  have hwa : DP (P a) k.+1 b=zz a :=
    jet_top_differential_constant hNY hZ (hzz haF) (hP haF) (hDPd (P a) k.+1 b).
  have hwb : DP (P b) k.+1 b=zz b :=
    norm_higher_differential_unique hN hNY hZ (hbase b hbF k.+1 (leqnn _)) (hzz hbF).
  rewrite hwa hwb subnn expr0 fact0 mulr1 divr1 (real_seminorm_subtract hZNk1.1).
  exact: (hunif a b ha hb (le_lt_trans hba_small hdd2)).
- (* i=k: the rate of the top differential *)
  subst i.
  have hab' : a+(b-a)=b by rewrite addrCA subrr addr0.
  have hHD : has_norm_higher_differential N ev ZN (fun _=>True) (P a) k (a+(b-a)) (DP (P a) k b).
    by rewrite hab'; exact: (hDPd (P a) k b).
  have hwa : DP (P a) k b=Dk a+T a (b-a) :=
    jet_top_differential_affine hNY hZ (hzz haF) (hP haF) (hDkf (hFB haF)) (hlift haF) hHD.
  have hwb : DP (P b) k b=Dk b :=
    norm_higher_differential_unique hN hNY hZ (hbase b hbF k (leqnSn _)) (hDkf (hFB hbF)).
  rewrite hwa hwb subSnn expr1 factS fact0 muln1 divr1 (real_seminorm_subtract hZNk.1).
  have -> : Dk b-(Dk a+T a (b-a))=Dk b-Dk a-T a (b-a) by rewrite opprD addrA.
  apply: (le_trans (hrateA a ha b (hFB hbF) hbr)).
  rewrite hab; exact: (ler_wpM2r (real_seminorm_nonnegative hN.1 _) (ltW heta_lt)).
Qed.
End JetFamily.
