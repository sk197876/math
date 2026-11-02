(** Federer (1969), 3.1.14, p. 226:
    the estimates ||D^i g(x)-D^i P_b(x)||<=M_i |x-b|^(k-i) rho(C,6|x-b|)
    and ||D^i P_b(x)-D^i P_a(x)||<=(3|x-a|)^(k-i) rho(C,2|x-a|)/(k-i)! for
    a in A, x in U with |x-a|<=1/4 and b=xi(x), together with the
    estimate on A itself. *)
From mathcomp Require Import all_boot all_order all_algebra boolp finmap classical_sets
  cardinality reals constructive_ereal topology ring lra.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP SymmetricForms
  PolynomialFunctions PolynomialRepresentations PolynomialTaylor
  SymmetricOperatorNormUP SymmetricOperatorNorm SymmetricOperatorBoundary
  ContinuousMultilinearUP ContinuousMultilinearNorm NormDifferentialUP
  NormHigherDifferentialUP NormHigherDifferentialLocal NormClassHigherUP NormClassHigherFields
  InnerNearestUP MetricClosedBalls
  FedererCoverRadius LipschitzRadiusOverlap EuclideanPartitionBallCoverUP
  EuclideanPartitionFamilyUP EuclideanPartitionOverlapNeighborhood
  WhitneyModulusUP WhitneyPolynomialDifferenceBound ScalarVectorLeibnizBound
  WhitneyNearestCenters WhitneyOverlapGeometry WhitneyExtensionFunction
  WhitneyDerivativeSums WhitneyFormBridge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section BoundaryEstimate.
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
Local Notation g := (whitney_extension P xi hfamily).
Local Notation Sx := (fun x=>lipschitz_radius_overlap S h 10 10 x).
Local Notation C a := (A `&` metric_closed_ball a 2).

(** Source for [whitney_sum_constant]:
    the sum over j of C(i,j) V_(i-j) 20^(i-j) 7^(k-j)/(k-j)!,
    collecting the factors of the estimate on Federer 3.1.14,
    p. 226, for a single centre s of S_x. *)
Definition whitney_sum_constant (i : nat) : R :=
  \sum_(j<i.+1) ('C(i,j))%:R*(V (i-j)%N*7^+(k-j)*20^+(i-j)/((k-j)`!)%:R).

(** Source for [whitney_nearest_constant]:
    the constant M_i=129^m sum_j C(i,j) V_(i-j) 20^(i-j) 7^(k-j)/(k-j)!,
    determined by m, k and V_0,...,V_i, Federer 3.1.14, p. 226. *)
Definition whitney_nearest_constant (i : nat) : R := 129^+m*whitney_sum_constant i.

(** Source for [whitney_sum_constant_nonnegative]:
    the constants are nonnegative, Federer 3.1.14, p. 226. *)
Lemma whitney_sum_constant_nonnegative i : 0<=whitney_sum_constant i.
Proof.
apply: sumr_ge0=>j _; apply: mulr_ge0; first exact: ler0n.
apply: divr_ge0; last exact: ler0n.
apply: mulr_ge0; last exact: exprn_ge0.
by apply: mulr_ge0; [exact: hV0|exact: exprn_ge0].
Qed.

(** Source for [whitney_nearest_constant_nonnegative]:
    M_i>=0, Federer 3.1.14, p. 226. *)
Lemma whitney_nearest_constant_nonnegative i : 0<=whitney_nearest_constant i.
Proof. exact: mulr_ge0 (exprn_ge0 _ _) (whitney_sum_constant_nonnegative i). Qed.

(** Source for [whitney_term_identity]:
    the factor h(x)^(j-i) [140h(x)]^(k-j) with 20h(x)=|x-b| equals
    20^(i-j) 7^(k-j) |x-b|^(k-i), Federer 3.1.14, p. 226. *)
Lemma whitney_term_identity (t rho c V0 : R) (i j : nat) : 0<t -> (j<=i)%N -> (i<=k)%N ->
  V0/(t/20)^+(i-j)*(rho*(7*t)^+(k-j)/c)=rho*t^+(k-i)*(V0*7^+(k-j)*20^+(i-j)/c).
Proof.
move=>ht hji hik.
have hkj : (k-j=(k-i)+(i-j))%N by rewrite addnBA // subnK.
have hc : t^+(i-j)/t^+(i-j)= 1 by apply: mulfV; exact: (expf_neq0 _ (lt0r_neq0 ht)).
rewrite hkj expr_div_n invf_div !exprD !exprMn.
rewrite -[RHS]mulr1 -hc; ring.
Qed.

(** Source for [whitney_modulus_pair_bound]:
    ||D^i P_c(b)-D^i P_b(b)||<=rho(C,delta) |c-b|^(k-i)/(k-i)! for
    c,b in C with |c-b|<=delta, including c=b, Federer 3.1.14,
    p. 225, from the definition of rho. *)
Lemma whitney_modulus_pair_bound (B : set X) (delta rho : R) (c b : X) i :
  0<=rho -> (whitney_modulus NY k P B delta<=rho%:E)%E -> B c -> B b ->
  N (c-b)<=delta -> (i<=k)%N ->
  (symmetric_operator_norm hN.1 NY
    (polynomial_taylor_coefficient (P c) i b-polynomial_taylor_coefficient (P b) i b)%R
    <=(rho*(N (c-b))^+(k-i)/((k-i)`!)%:R)%:E)%E.
Proof.
move=>hrho hmod hc hb hd hi.
have h0 := real_seminorm_nonnegative hN.1 (c-b).
rewrite le_eqVlt in h0; case/orP: h0=>[/eqP h0|hpos].
- have hcb : c=b by apply: subr0_eq; apply: hN.2; rewrite -h0.
  rewrite hcb subrr (symmetric_operator_zero hN.1 hNY.1) lee_fin.
  apply: divr_ge0; last exact: ler0n.
  apply: mulr_ge0; first exact: hrho.
  exact: exprn_ge0 (real_seminorm_nonnegative hN.1 _).
- exact: (whitney_modulus_bound hNY hmod hi hc hb hpos hd).
Qed.

(** Source for [whitney_translated_pair_bound]:
    ||D^j P_c(x)-D^j P_b(x)||<=[(|x-b|+|c-b|)^(k-j)/(k-j)!] rho(C,delta)
    for c,b in C with |c-b|<=delta, Federer 3.1.14, p. 226,
    the first displayed estimate. *)
Lemma whitney_translated_pair_bound (B : set X) (delta rho : R) (c b x : X) j :
  B `<=` A -> 0<=rho -> (whitney_modulus NY k P B delta<=rho%:E)%E -> B c -> B b ->
  N (c-b)<=delta -> (j<=k)%N ->
  (symmetric_operator_norm hN.1 NY
    (polynomial_taylor_coefficient (P c) j x-polynomial_taylor_coefficient (P b) j x)%R
    <=(rho*(N (x-b)+N (c-b))^+(k-j)/((k-j)`!)%:R)%:E)%E.
Proof.
move=>hBA hrho hmod hc hb hd hj.
have hx : b+(x-b)=x by rewrite addrC subrK.
have hres := whitney_polynomial_difference_bound hNY (x-b) (hdeg (hBA c hc)) (hdeg (hBA b hb))
  (real_seminorm_nonnegative hN.1 (c-b)) hrho
  (fun i hi=>whitney_modulus_pair_bound hrho hmod hc hb hd hi) hj.
by rewrite hx in hres.
Qed.

(** Source for [whitney_center_in_cap]:
    b=xi(x) lies in C=A cap B(a,2) when |x-a|<=1/4,
    Federer 3.1.14, p. 226. *)
Lemma whitney_center_in_cap (a x : X) : A a -> U x -> N (x-a)<=1/4 -> C a (xi x).
Proof.
move=>ha hx hxa.
have [_ [_ [_ hba]]] := whitney_nearest_geometry hne hxi ha hx hxa.
split; first exact: (inner_nearest_member_law (hxi x)).
rewrite /metric_closed_ball /= inner_metric_distanceE (real_seminorm_subtract hN.1); lra.
Qed.

(** Source for [whitney_overlap_center_in_cap]:
    xi(s) lies in C for s in S_x, Federer 3.1.14, p. 226. *)
Lemma whitney_overlap_center_in_cap (a x s : X) : A a -> U x -> N (x-a)<=1/4 -> Sx x s ->
  C a (xi s).
Proof.
move=>ha hx hxa hs.
have [_ [_ [hsa _]]] := whitney_overlap_geometry hA hne hxi hS ha hx hxa hs.
split; first exact: (inner_nearest_member_law (hxi s)).
by rewrite /metric_closed_ball /= inner_metric_distanceE (real_seminorm_subtract hN.1).
Qed.

(** Source for [whitney_summand_derivative_bound]:
    the bound for a single centre s of S_x of the ith
    differential of v_s (P_{xi(s)}-P_b) at x, Federer 3.1.14, p. 226:
    sum_j C(i,j) V_(i-j) h(x)^(j-i) [140h(x)]^(k-j) rho(C,120h(x))/(k-j)!. *)
Lemma whitney_summand_derivative_bound i (a x s : X) (rho : R) (z : Z i) :
  (i<=k)%N -> A a -> U x -> N (x-a)<=1/4 -> Sx x s -> 0<=rho ->
  (whitney_modulus NY k P (C a) (6*N (x-xi x))<=rho%:E)%E ->
  has_norm_higher_differential N ev ZN (fun _=>True)
    (whitney_difference_summand P xi v (P (xi x)) s) i x z ->
  @ZN i z<=rho*(N (x-xi x))^+(k-i)*whitney_sum_constant i.
Proof.
move=>hi ha hx hxa hs hrho hmod hz.
have hsS : S s := hs.1.
have [hpos [_ [hrad _]]] := whitney_nearest_geometry hne hxi ha hx hxa.
have [_ [_ [_ hsb]]] := whitney_overlap_geometry hA hne hxi hS ha hx hxa hs.
have hbC := whitney_center_in_cap ha hx hxa.
have hcC := whitney_overlap_center_in_cap ha hx hxa hs.
have hCA : C a `<=` A by move=>y [hy _].
have hU : forall y, U y -> norm_domain_interior N U y.
  exact: (inner_open_norm_domain (whitney_union_open hA)).
have [Dv [hDv _]] := norm_class_higher_fields hN (@scalar_absolute_value_norm R) hW
  (partition_family_global_smooth hfamily hsS k).
have hhx : h x=N (x-xi x)/20 by lra.
have hF : forall j, (j<=k)%N -> @WN j (Dv j x)<=V j/(h x)^+j.
  move=>j hj; apply: (hV hsS hx).
  apply: (norm_higher_differential_open_restriction hN (@scalar_absolute_value_norm R) hW
    (v s) (fun _ _=>I) hU hx (Dv j x)).1.
  exact: (hDv j hj x I).
have hG : forall j, (j<=k)%N -> @ZN j (DP (P (xi s)) j x-DP (P (xi x)) j x)<=
    rho*(7*N (x-xi x))^+(k-j)/((k-j)`!)%:R.
  move=>j hj.
  apply: (whitney_coefficient_difference_bound hNY hZ hDP).
  apply: le_trans (whitney_translated_pair_bound x hCA hrho hmod hcC hbC hsb hj) _.
  rewrite lee_fin; apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
  have h1 : 0<=N (x-xi x)+N (xi s-xi x).
    exact: addr_ge0 (real_seminorm_nonnegative hN.1 _) (real_seminorm_nonnegative hN.1 _).
  have h2 : 0<=7*N (x-xi x) := mulr_ge0 (ler0n _ _) (real_seminorm_nonnegative hN.1 _).
  apply: ler_pM hrho (exprn_ge0 _ h1) (lexx rho) _.
  apply: (lerXn2r _ h1 h2); lra.
have hleib := norm_scalar_vector_higher_differential_bound hN hNY hZ hW (A:=fun _=>True)
  (phi:=v s) (f:=fun y : X=>P (xi s) y-P (xi x) y) (k:=k) (a:=x)
  (Dphi:=fun j=>Dv j x) (Df:=fun j=>DP (P (xi s)) j x-DP (P (xi x)) j x)
  (F:=fun l=>V l/(h x)^+l) (G:=fun j=>rho*(7*N (x-xi x))^+(k-j)/((k-j)`!)%:R) (i:=i) (z:=z) I
  (partition_family_global_smooth hfamily hsS k)
  (whitney_polynomial_difference_class hNY hZ (P (xi s)) (P (xi x))
    (@whitney_whole_space_interior R m) k)
  (fun j hj=>hDv j hj x I)
  (fun j _=>whitney_polynomial_difference_field hNY hZ hDPd (P (xi s)) (P (xi x)) j x)
  hF hG hi hz.
have hsum : \sum_(j<i.+1) ('C(i,j))%:R*(V (i-j)%N/(h x)^+(i-j)*
    (rho*(7*N (x-xi x))^+(k-j)/((k-j)`!)%:R))=
    rho*(N (x-xi x))^+(k-i)*whitney_sum_constant i.
  rewrite /whitney_sum_constant big_distrr; apply: eq_bigr=>j _.
  by rewrite hhx (whitney_term_identity rho ((k-j)`!)%:R (V (i-j)%N) hpos (leq_ord j) hi) mulrCA.
rewrite -hsum; exact: hleib.
Qed.

(** Source for [whitney_nearest_estimate]:
    ||D^i g(x)-D^i P_b(x)||<=M_i |x-b|^(k-i) rho(C,6|x-b|) for
    a in A, x in U with |x-a|<=1/4 and b=xi(x), Federer 3.1.14,
    p. 226, by summing the bounds over the at most 129^m
    centres of S_x. *)
Theorem whitney_nearest_estimate i (a x : X) (rho : R) (z : Z i) :
  (i<=k)%N -> A a -> U x -> N (x-a)<=1/4 -> 0<=rho ->
  (whitney_modulus NY k P (C a) (6*N (x-xi x))<=rho%:E)%E ->
  has_norm_higher_differential N ev ZN U g i x z ->
  @ZN i (z-DP (P (xi x)) i x)<=whitney_nearest_constant i*rho*(N (x-xi x))^+(k-i).
Proof.
move=>hi ha hx hxa hrho hmod hz.
have hU : forall y, U y -> norm_domain_interior N U y.
  exact: (inner_open_norm_domain (whitney_union_open hA)).
have hzq : has_norm_higher_differential N ev ZN U (P (xi x)) i x (DP (P (xi x)) i x).
  apply: (norm_higher_differential_open_restriction hN hNY hZ (P (xi x)) (fun _ _=>I) hU hx
    (DP (P (xi x)) i x)).1.
  exact: hDPd.
have hsummand : forall s, exists D : forall j, X->Z j, S s -> forall j, (j<=k)%N -> forall y,
    has_norm_higher_differential N ev ZN (fun _=>True)
      (whitney_difference_summand P xi v (P (xi x)) s) j y (D j y).
  move=>s; case: (pselect (S s))=>[hs|hs].
  - have [D [hD _]] := norm_class_higher_fields hN hNY hZ
      (whitney_difference_summand_class hNY hZ hW P xi hfamily (P (xi x)) hs k).
    by exists D=>_ j hj y; exact: (hD j hj y I).
  - by exists (fun _ _=>0).
have [Dsum hDsum] := choice hsummand.
have hdiff := whitney_derivative_difference_sum hNY hZ hW hA hS hx hz hzq
  (D:=fun s y=>Dsum s i y) (fun s hs y=>hDsum s hs i hi y).
rewrite hdiff.
set fs := whitney_overlap_fset A S x.
set c := rho*(N (x-xi x))^+(k-i)*whitney_sum_constant i.
have hZNi := continuous_multilinear_norm_is_norm hNY (@hZ i).
have hc0 : 0<=c.
  apply: mulr_ge0; last exact: whitney_sum_constant_nonnegative.
  exact: mulr_ge0 hrho (exprn_ge0 _ (real_seminorm_nonnegative hN.1 _)).
have hseq : forall (r : seq X) (F : X->Z i), @ZN i (\sum_(s <- r) F s)<=\sum_(s <- r) @ZN i (F s).
  move=>r F; elim: r=>[|s r ih]; first by rewrite !big_nil (real_seminorm_zero hZNi.1).
  rewrite !big_cons; apply: le_trans (real_seminorm_triangle hZNi.1 _ _) _.
  exact: lerD (lexx _) ih.
have hterm : forall s, s \in fs -> @ZN i (Dsum s i x)<=c.
  move=>s hs.
  have hsx : Sx x s.
    move: hs; rewrite /fs /whitney_overlap_fset in_fset_set; last exact: (partition_ball_overlap_finite hS hx).
    exact: set_mem.
  exact: (whitney_summand_derivative_bound hi ha hx hxa hsx hrho hmod (hDsum s hsx.1 i hi x)).
have hcard : (#|` fs|)%:R<=(129 : R)^+m := partition_ball_overlap_bound hS hx.
apply: (le_trans (hseq (enum_fset fs) (fun s=>Dsum s i x)) _).
have hbound : \sum_(s <- fs) @ZN i (Dsum s i x)<=(#|` fs|)%:R*c.
  rewrite card_fset_sum1 natr_sum mulr_suml big_seq [X in _<=X]big_seq.
  apply: ler_sum=>s hs; rewrite mul1r; exact: hterm.
have hfinal : (#|` fs|)%:R*c<=129^+m*c := ler_wpM2r hc0 hcard.
have heq : 129^+m*c=whitney_nearest_constant i*rho*(N (x-xi x))^+(k-i).
  by rewrite /whitney_nearest_constant /c; ring.
rewrite -heq; exact: (le_trans hbound hfinal).
Qed.

(** Source for [whitney_nearest_point_estimate]:
    ||D^i P_b(x)-D^i P_a(x)||<=(3|x-a|)^(k-i) rho(C,2|x-a|)/(k-i)!
    for a in A, x in U with |x-a|<=1/4 and b=xi(x),
    Federer 3.1.14, p. 226, from |x-b|<=|x-a| and |b-a|<=2|x-a|. *)
Theorem whitney_nearest_point_estimate i (a x : X) (rho : R) :
  (i<=k)%N -> A a -> U x -> N (x-a)<=1/4 -> 0<=rho ->
  (whitney_modulus NY k P (C a) (2*N (x-a))<=rho%:E)%E ->
  @ZN i (DP (P (xi x)) i x-DP (P a) i x)<=rho*(3*N (x-a))^+(k-i)/((k-i)`!)%:R.
Proof.
move=>hi ha hx hxa hrho hmod.
have [_ [_ [_ hba]]] := whitney_nearest_geometry hne hxi ha hx hxa.
have hbC := whitney_center_in_cap ha hx hxa.
have haC : C a a.
  split; first exact ha.
  rewrite /metric_closed_ball /= inner_metric_distanceE subrr (real_seminorm_zero hN.1).
  exact: ler0n.
have hCA : C a `<=` A by move=>y [hy _].
apply: (whitney_coefficient_difference_bound hNY hZ hDP).
apply: le_trans (whitney_translated_pair_bound x hCA hrho hmod hbC haC hba hi) _.
rewrite lee_fin; apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
have h1 : 0<=N (x-a)+N (xi x-a).
  exact: addr_ge0 (real_seminorm_nonnegative hN.1 _) (real_seminorm_nonnegative hN.1 _).
have h2 : 0<=3*N (x-a) := mulr_ge0 (ler0n _ _) (real_seminorm_nonnegative hN.1 _).
apply: ler_pM hrho (exprn_ge0 _ h1) (lexx rho) _.
apply: (lerXn2r _ h1 h2); lra.
Qed.

(** Source for [whitney_point_estimate]:
    on A itself, ||D^i P_x(x)-D^i P_a(x)||<=|x-a|^(k-i) rho(C,|x-a|)/(k-i)!
    for a, x in A with |x-a|<=2, Federer 3.1.14, p. 225, directly from
    the definition of rho; this supplies the induction on p. 227 at
    points of A. *)
Theorem whitney_point_estimate i (a x : X) (rho : R) :
  (i<=k)%N -> A a -> A x -> N (x-a)<=2 -> 0<=rho ->
  (whitney_modulus NY k P (C a) (N (x-a))<=rho%:E)%E ->
  @ZN i (DP (P x) i x-DP (P a) i x)<=rho*(N (x-a))^+(k-i)/((k-i)`!)%:R.
Proof.
move=>hi ha hxA hxa hrho hmod.
have hZNi := continuous_multilinear_norm_is_norm hNY (@hZ i).
have haC : C a a.
  split; first exact ha.
  rewrite /metric_closed_ball /= inner_metric_distanceE subrr (real_seminorm_zero hN.1).
  exact: ler0n.
have hxC : C a x.
  split; first exact hxA.
  by rewrite /metric_closed_ball /= inner_metric_distanceE (real_seminorm_subtract hN.1).
rewrite -(real_seminorm_negate hZNi.1) opprB.
apply: (whitney_coefficient_difference_bound hNY hZ hDP).
have hd : N (a-x)<=N (x-a) by rewrite (real_seminorm_subtract hN.1).
apply: le_trans (whitney_modulus_pair_bound hrho hmod haC hxC hd hi) _.
rewrite lee_fin (real_seminorm_subtract hN.1 a x); exact: lexx.
Qed.
End BoundaryEstimate.
