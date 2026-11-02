(** Federer (1969), 3.1.14, pp. 226–227:
    the induction with respect to i. The global fields equal
    to D^i P_a(a) on A and to the actual differentials of g|U
    on U are the actual higher differentials of g on R^m and
    are continuous, so that g is of class k with the required
    boundary values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology ring lra.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP SymmetricForms
  PolynomialFunctions PolynomialRepresentations PolynomialTaylor
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearZero
  NormDifferentialUP NormClassOneUP NormHigherDifferentialUP NormHigherDifferentialFields
  NormHigherDifferentialUnique NormHigherDifferentialLocal NormClassHigherUP NormClassHigherFields
  NormClassHigherDerivative NormHigherSymmetricFormUP
  InnerNearestUP MetricClosedBalls EuclideanClosedBallCompact
  FedererCoverRadius LipschitzRadiusOverlap EuclideanPartitionBallCoverUP
  EuclideanPartitionFamilyUP EuclideanPartitionOverlapNeighborhood
  WhitneyModulusUP WhitneyNearestCenters WhitneyOverlapGeometry WhitneyExtensionFunction
  WhitneyFormBridge WhitneyBoundaryEstimate FiniteInnerPolynomialSmoothness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section WhitneyInduction.
Variable R : realType.
Variable m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable Y : lmodType R.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space N NY (@ev i) (@ZN i).
Variable W : nat->lmodType R.
Variable ew : forall i, {ffun 'I_i->R_n R m}->Hom (W i) R^o.
Variable WN : forall i, W i->R.
Hypothesis hW : forall i, is_continuous_multilinear_space N (fun t : R^o=>`|t|) (@ew i) (@WN i).
Variable A : set X.
Hypothesis hA : closed A.
Hypothesis hne : A !=set0.
Variable k : nat.
Variable P : X->PolynomialFunction (R_n R m) Y.
Hypothesis hdeg : forall a, A a -> (polynomial_degree (P a)<=k)%N.
Variable xi : X->X.
Hypothesis hxi : forall s, is_inner_nearest (@euclidean_inner_productP R m) s A (xi s).
Local Notation Phi := ([set (~` A : set X)]).
Local Notation U := (\bigcup_(T in Phi) T).
Local Notation h := (federer_cover_radius Phi).
Variable S : set X.
Variables (sigma : X->R) (v : X->X->R).
Hypothesis hS : is_federer_partition_ball_cover Phi S.
Hypothesis hfamily : is_euclidean_partition_family ew WN Phi S sigma v.
Variable V : nat->R.
Hypothesis hV0 : forall i, 0<=V i.
Hypothesis hV : forall s, S s -> forall i x (z : W i), U x ->
  has_norm_higher_differential N ew WN U (v s) i x z -> @WN i z<=V i/(h x)^+i.
Variable DP : PolynomialFunction (R_n R m) Y->forall i, X->Z i.
Hypothesis hDP : forall Q i x u, @ev i u (DP Q i x)=polynomial_taylor_coefficient Q i x [tuple u j | j<i].
Hypothesis hDPd : forall (Q : PolynomialFunction (R_n R m) Y) i x,
  has_norm_higher_differential N ev ZN (fun _=>True) Q i x (DP Q i x).
Hypothesis hmodulus : forall B : set X, B `<=` A -> compact B -> forall e : R, 0<e ->
  exists delta : R, 0<delta /\ forall d, 0<d -> d<=delta -> (whitney_modulus NY k P B d<=e%:E)%E.
Local Notation g := (whitney_extension P xi hfamily).
Local Notation C a := (A `&` metric_closed_ball a 2).
Variable DU : forall i, X->Z i.
Hypothesis hDU : forall i, (i<=k)%N -> forall x, U x ->
  has_norm_higher_differential N ev ZN U g i x (DU i x).
Hypothesis hDUc : forall i, (i<=k)%N -> norm_class_zero N (@ZN i) U (DU i).

(** Source for [whitney_field]:
    the candidate ith differential of g on R^m: D^i P_x(x) at
    points x of A and the actual differential of g|U on U,
    Federer 3.1.14, pp. 225–227. *)
Definition whitney_field (i : nat) (x : X) : Z i :=
  if pselect (A x) then DP (P x) i x else DU i x.

(** Source for [whitney_field_on]:
    the prescribed values on A, Federer 3.1.14, p. 225. *)
Lemma whitney_field_on i x : A x -> whitney_field i x=DP (P x) i x.
Proof. by move=>hx; rewrite /whitney_field; case: pselect. Qed.

(** Source for [whitney_field_off]:
    the values on U, Federer 3.1.14, p. 226. *)
Lemma whitney_field_off i x : U x -> whitney_field i x=DU i x.
Proof.
move=>hx; rewrite /whitney_field; case: (pselect (A x))=>[hxA|hxA]; last by [].
by exfalso; case: hx=>T -> hxT; exact: (hxT hxA).
Qed.

(** Source for [whitney_union_member]:
    U=R^m-A contains every point outside A, Federer 3.1.14, p. 225. *)
Lemma whitney_union_member x : ~ A x -> U x.
Proof. by move=>hx; exists (~` A). Qed.

(** Source for [whitney_cap_subset]:
    C=A cap B(a,2) is a subset of A, Federer 3.1.14, p. 226. *)
Lemma whitney_cap_subset (a : X) : C a `<=` A.
Proof. by move=>y [hy _]. Qed.

(** Source for [whitney_cap_compact]:
    C=A cap B(a,2) is compact, being closed and bounded in R^m,
    Federer 3.1.14, p. 226. *)
Lemma whitney_cap_compact (a : X) : compact (C a).
Proof.
apply: (subclosed_compact (B:=metric_closed_ball a 2)).
- exact: (closedI hA (@metric_closed_ball_closed R X a 2)).
- exact: (@euclidean_closed_metric_ball_compact R m a 2).
- by move=>y [_ hy].
Qed.

(** Source for [whitney_field_little_o]:
    lim_{x->a} ||D^i g(x)-D^i P_a(x)||/|x-a|^(k-i)=0 for a in A,
    Federer 3.1.14, p. 227, from the two estimates of p. 226 and
    the hypothesis rho(C,delta)->0 for compact C. *)
Theorem whitney_field_little_o i (a : X) (e : R) : (i<=k)%N -> A a -> 0<e ->
  exists d : R, 0<d /\ forall x, N (x-a)<d ->
    @ZN i (whitney_field i x-DP (P a) i x)<=e*(N (x-a))^+(k-i).
Proof.
move=>hi ha he.
have hZNi := continuous_multilinear_norm_is_norm hNY (@hZ i).
set K := whitney_nearest_constant m k V i+3^+(k-i)+1.
have hK1 : 1<=K.
  have := whitney_nearest_constant_nonnegative m k hV0 i.
  have := exprn_ge0 (k-i) (ler0n R 3); rewrite /K; lra.
have hK0 : 0<K by lra.
set e' := e/K.
have he' : 0<e' by exact: divr_gt0.
have he'e : e'<=e.
  rewrite /e' ler_pdivrMr //; exact: ler_peMr (ltW he) hK1.
have hKe : e=K*e' by rewrite /e' mulrCA mulfV ?mulr1 //; exact: lt0r_neq0.
have [delta [hdelta hmod]] := hmodulus (@whitney_cap_subset a) (@whitney_cap_compact a) he'.
exists (Num.min (1/4) (delta/6)); split.
  by rewrite lt_min; apply/andP; split; [lra|apply: divr_gt0=>//; rewrite ltr0n].
move=>x hu; rewrite lt_min in hu; case/andP: hu=>hu1 hu2.
have hx1 : N (x-a)<=1/4 by exact: ltW.
have hN0 := real_seminorm_nonnegative hN.1 (x-a).
have hpow0 : 0<=(N (x-a))^+(k-i) := exprn_ge0 _ hN0.
have hfact : (1 : R)<=((k-i)`!)%:R by rewrite ler1n fact_gt0.
case: (pselect (A x))=>[hxA|hxU].
- rewrite (whitney_field_on i hxA).
  have h0 := hN0; rewrite le_eqVlt in h0; case/orP: h0=>[/eqP h0|hpos].
  + have hxa : x=a by apply: subr0_eq; apply: hN.2; rewrite -h0.
    rewrite hxa !subrr (real_seminorm_zero hZNi.1).
    exact: mulr_ge0 (ltW he) (exprn_ge0 _ (real_seminorm_nonnegative hN.1 _)).
  + have hmod' : (whitney_modulus NY k P (C a) (N (x-a))<=e'%:E)%E by apply: hmod=>//; lra.
    have hx2 : N (x-a)<=2 by lra.
    have hest := whitney_point_estimate hNY hZ hDP hi ha hxA hx2 (ltW he') hmod'.
    apply: (le_trans hest _).
    rewrite ler_pdivrMr; last by rewrite ltr0n fact_gt0.
    exact: (le_trans (ler_wpM2r hpow0 he'e) (ler_peMr (mulr_ge0 (ltW he) hpow0) hfact)).
- have hxU' := whitney_union_member hxU.
  rewrite (whitney_field_off i hxU').
  have [hpos [hle [hrad hba]]] := whitney_nearest_geometry hne hxi ha hxU' hx1.
  have hmod1 : (whitney_modulus NY k P (C a) (6*N (x-xi x))<=e'%:E)%E by apply: hmod; lra.
  have hmod2 : (whitney_modulus NY k P (C a) (2*N (x-a))<=e'%:E)%E by apply: hmod; lra.
  have h1 := whitney_nearest_estimate hNY hZ hW hA hne hdeg hxi hS hV0 hV hDP hDPd hi ha hxU'
    hx1 (ltW he') hmod1 (hDU hi hxU').
  have h2 := whitney_nearest_point_estimate hNY hZ hne hdeg hxi hDP hi ha hxU' hx1 (ltW he') hmod2.
  have hsplit : DU i x-DP (P a) i x=
      (DU i x-DP (P (xi x)) i x)+(DP (P (xi x)) i x-DP (P a) i x).
    by rewrite addrA subrK.
  rewrite hsplit.
  apply: (le_trans (real_seminorm_triangle hZNi.1 _ _) _).
  apply: (le_trans (lerD h1 h2) _).
  set p := (N (x-a))^+(k-i).
  have ht : (N (x-xi x))^+(k-i)<=p := lerXn2r (k-i) (ltW hpos) hN0 hle.
  have hM := whitney_nearest_constant_nonnegative m k hV0 i.
  have h3 : whitney_nearest_constant m k V i * e' * (N (x-xi x))^+(k-i)<=
      whitney_nearest_constant m k V i*e' * p.
    exact: (ler_wpM2l (mulr_ge0 hM (ltW he')) ht).
  have hq : 0<=e' * p := mulr_ge0 (ltW he') hpow0.
  have h4 : e'*(3*N (x-a))^+(k-i)/((k-i)`!)%:R<=3^+(k-i) * e' * p.
    rewrite exprMn -/p ler_pdivrMr; last by rewrite ltr0n fact_gt0.
    rewrite mulrCA mulrA.
    exact: (ler_peMr (mulr_ge0 (mulr_ge0 (exprn_ge0 _ (ler0n _ _)) (ltW he')) hpow0) hfact).
  apply: (le_trans (lerD h3 h4) _).
  have -> : e* p=whitney_nearest_constant m k V i*e' * p+3^+(k-i) * e' * p+e' * p.
    by rewrite hKe /K; ring.
  rewrite lerDl; exact: hq.
Qed.

(** Source for [whitney_field_differential]:
    by induction on i<=k, D^i g exists on R^m and equals the
    field: on U by the local agreement with g|U, and at a in A
    because D^i g(x)-D^i P_a(x)=o(|x-a|) implies that D^i g is
    differentiable at a with D^(i+1) g(a)=D^(i+1) P_a(a),
    Federer 3.1.14, p. 227. *)
Theorem whitney_field_differential i : (i<=k)%N ->
  forall x, has_norm_higher_differential N ev ZN (fun _=>True) g i x (whitney_field i x).
Proof.
have hU : forall y, U y -> norm_domain_interior N U y.
  exact: (inner_open_norm_domain (whitney_union_open hA)).
elim: i=>[|i ih] hi x.
- case: (pselect (A x))=>[hxA|hxU].
  + rewrite (whitney_field_on 0%N hxA); split; first exact I.
    rewrite (whitney_extension_on P xi hfamily hxA); exact: (hDPd (P x) 0%N x).2.
  + have hxU' := whitney_union_member hxU.
    rewrite (whitney_field_off 0%N hxU'); split; first exact I.
    exact: (hDU hi hxU').2.
- have hi' : (i<=k)%N := ltnW hi.
  have hZNi := continuous_multilinear_norm_is_norm hNY (@hZ i).
  case: (pselect (A x))=>[hxA|hxU]; last first.
  + have hxU' := whitney_union_member hxU.
    rewrite (whitney_field_off i.+1 hxU').
    exact: (norm_higher_differential_open_restriction hN hNY hZ g (fun _ _=>I) hU hxU'
      (DU i.+1 x)).2 (hDU hi hxU').
  + rewrite (whitney_field_on i.+1 hxA).
    have [L [hL heL]] := norm_higher_differential_field_step_elim hN (A:=fun _=>True)
      (D:=DP (P x) i) (fun y _=>hDPd (P x) i y) (hDPd (P x) i.+1 x).
    apply: (norm_higher_differential_field_step hN hNY hZ (D:=whitney_field i) (L:=L)).
    * by move=>y _; exact: (ih hi' y).
    * split.
      - exact: (whitney_whole_space_interior x I).
      - exact: (norm_differential_bounded hL).
      - move=>e he.
        have he2 : 0<e/2 by exact: divr_gt0.
        have [d1 [hd1 hrem]] := norm_differential_remainder hL he2.
        have [d2 [hd2 hlo]] := whitney_field_little_o hi' hxA he2.
        exists (Num.min d1 (Num.min d2 1)); split.
          by rewrite !lt_min hd1 hd2 ltr01.
        move=>u _ hu.
        rewrite !lt_min in hu; case/andP: hu=>hu1 /andP [hu2 hu3].
        have hux : (x+u)-x=u by rewrite addrAC subrr add0r.
        have hsplit : whitney_field i (x+u)-whitney_field i x-L u=
            (whitney_field i (x+u)-DP (P x) i (x+u))+(DP (P x) i (x+u)-DP (P x) i x-L u).
          by rewrite (whitney_field_on i hxA) !addrA subrK.
        rewrite hsplit.
        apply: (le_trans (real_seminorm_triangle hZNi.1 _ _) _).
        have h1 := hlo (x+u); rewrite hux in h1; have h1' := h1 hu2.
        have h2 := hrem u I hu1.
        have hki : (0<k-i)%N by rewrite subn_gt0.
        have hNu0 := real_seminorm_nonnegative hN.1 u.
        have hpow : (N u)^+(k-i)<=N u.
          rewrite -(prednK hki) exprS.
          exact: (ler_piMr hNu0 (exprn_ile1 _ hNu0 (ltW hu3))).
        have h1'' : @ZN i (whitney_field i (x+u)-DP (P x) i (x+u))<=e/2*N u.
          exact: (le_trans h1' (ler_wpM2l (ltW he2) hpow)).
        apply: (le_trans (lerD h1'' h2) _).
        rewrite -mulrDl -splitr; exact: lexx.
    * exact heL.
Qed.

(** Source for [whitney_polynomial_field_continuous]:
    the coefficient fields D^i Q of a polynomial are continuous,
    Federer 3.1.11, p. 221, as used in 3.1.14, p. 227. *)
Lemma whitney_polynomial_field_continuous (Q : PolynomialFunction (R_n R m) Y) i :
  norm_class_zero N (@ZN i) (fun _=>True) (DP Q i).
Proof.
have hsmooth := @finite_inner_polynomial_smooth R (R_n R m) Y _ (@euclidean_inner_productP R m)
  NY hNY m _ (@coordinate_basisP R m) Z ev ZN hZ (fun _=>True) (@whitney_whole_space_interior R m) Q i.
have [D [hD hDc]] := norm_class_higher_fields hN hNY hZ hsmooth.
apply: (norm_class_zero_domain_agreement (f:=D i)); last exact: (hDc i (leqnn i)).
move=>x _; exact: (norm_higher_differential_unique hN hNY hZ (hD i (leqnn i) x I) (hDPd Q i x)).
Qed.

(** Source for [whitney_field_continuous]:
    D^i g is continuous at every point: on U by the smoothness of
    g|U, at a in A by the estimate of p. 227 with exponent k-i>=0
    and the continuity of D^i P_a, Federer 3.1.14, p. 227. *)
Theorem whitney_field_continuous i : (i<=k)%N ->
  norm_class_zero N (@ZN i) (fun _=>True) (whitney_field i).
Proof.
move=>hi a _.
have hZNi := continuous_multilinear_norm_is_norm hNY (@hZ i).
split; first exact: (whitney_whole_space_interior a I).
move=>e he.
case: (pselect (A a))=>[haA|haU].
- have he3 : 0<e/3 by exact: divr_gt0.
  have [d1 [hd1 hlo]] := whitney_field_little_o hi haA he3.
  have [_ hc] := @whitney_polynomial_field_continuous (P a) i a I.
  have [d2 [hd2 hcont]] := hc (e/3) he3.
  exists (Num.min d1 (Num.min d2 1)); split; first by rewrite !lt_min hd1 hd2 ltr01.
  move=>u _ hu; rewrite !lt_min in hu; case/andP: hu=>hu1 /andP [hu2 hu3].
  have hux : (a+u)-a=u by rewrite addrAC subrr add0r.
  have hsplit : whitney_field i (a+u)-whitney_field i a=
      (whitney_field i (a+u)-DP (P a) i (a+u))+(DP (P a) i (a+u)-DP (P a) i a).
    by rewrite (whitney_field_on i haA) addrA subrK.
  rewrite hsplit.
  apply: (le_lt_trans (real_seminorm_triangle hZNi.1 _ _) _).
  have h1 := hlo (a+u); rewrite hux in h1; have h1' := h1 hu1.
  have hNu0 := real_seminorm_nonnegative hN.1 u.
  have hpow : (N u)^+(k-i)<=1 := exprn_ile1 _ hNu0 (ltW hu3).
  have h1'' : @ZN i (whitney_field i (a+u)-DP (P a) i (a+u))<=e/3.
    apply: (le_trans h1' _); rewrite -[X in _<=X]mulr1; exact: (ler_wpM2l (ltW he3) hpow).
  have h2 := hcont u I hu2.
  lra.
- have haU' := whitney_union_member haU.
  have hc0 : norm_class_zero N (@ZN i) U (DU i) := hDUc hi.
  have [[r [hr hball]] hc] := hc0 a haU'.
  have [d [hd hcont]] := hc e he.
  exists (Num.min d r); split; first by rewrite lt_min hd hr.
  move=>u _ hu; rewrite lt_min in hu; case/andP: hu=>hu1 hu2.
  have hau : U (a+u) := hball u hu2.
  rewrite (whitney_field_off i hau) (whitney_field_off i haU').
  exact: (hcont u hau hu1).
Qed.

(** Source for [whitney_extension_continuous]:
    g is continuous on R^m, Federer 3.1.14, p. 227, since
    g(x) is the value of the field of order zero. *)
Theorem whitney_extension_continuous : norm_class_zero N NY (fun _=>True) g.
Proof.
have hF0 := whitney_field_differential (leq0n k).
have hc := whitney_field_continuous (leq0n k).
have hg x : g x=@ev 0%N [ffun=>0] (whitney_field 0%N x) := esym (hF0 x).2.
move=>a _; split; first exact: (whitney_whole_space_interior a I).
move=>e he.
have [_ hca] := hc a I.
have [d [hd hcont]] := hca e he.
exists d; split; first exact hd.
move=>u _ hu.
rewrite !hg -raddfB -(continuous_multilinear_zero_norm hNY (@hZ 0%N)).
exact: (hcont u I hu).
Qed.

(** Source for [whitney_extension_class_higher]:
    g is of class k on R^m, Federer 3.1.14, p. 227. *)
Theorem whitney_extension_class_higher : norm_class_higher N NY ev ZN (fun _=>True) g k.
Proof.
split; first exact: whitney_extension_continuous.
exists (whitney_field k); split.
- by move=>x _; exact: (whitney_field_differential (leqnn k) x).
- exact: (whitney_field_continuous (leqnn k)).
Qed.

(** Source for [whitney_extension_boundary_forms]:
    D^i g(a)=D^i P_a(a) for i=0,...,k and a in A,
    Federer 3.1.14, p. 225, the conclusion of the theorem. *)
Theorem whitney_extension_boundary_forms (a : X) i : A a -> (i<=k)%N ->
  is_norm_higher_differential_form N ev ZN (fun _=>True) g i a
    (polynomial_taylor_coefficient (P a) i a).
Proof.
move=>ha hi; exists (whitney_field i a); split.
- exact: (whitney_field_differential hi a).
- move=>u; rewrite (whitney_field_on i ha); exact: hDP.
Qed.
End WhitneyInduction.
