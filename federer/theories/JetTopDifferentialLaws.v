(** Federer (1969), 3.1.15, p. 228: the two top differentials of the
    (k+1)-jet. For a polynomial of degree at most k+1, the coefficient
    S_(k+1) of 1.10.4, p. 46, is the same at every point, and the
    coefficient S_k is affine. Applied to the (k+1)-jet P_a of f at a,
    these give D^(k+1)P_a(b)=D^(k+1)f(a) and
    D^k P_a(a+h)=D^k f(a)+<h,D D^k f(a)>, the two identities entering the
    computations of D^k P_a(b)-D^k P_b(b) and D^(k+1)P_a(b)-D^(k+1)P_b(b)
    on p. 228. The jet laws are those of 3.1.11, p. 221. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SymmetricForms SymmetricFormSum
  Graded GradedDegree PolynomialFunctions PolynomialRepresentations PolynomialTaylorTerms
  PolynomialTaylorCoefficients PolynomialTaylorTermContinuity PolynomialTaylorTransform
  PolynomialTaylor PolynomialTaylorExactExpansion MultilinearSuccessorArguments
  ContinuousMultilinearUP ContinuousMultilinearNorm NormDifferentialUP
  NormHigherDifferentialUP NormHigherDifferentialUnique
  FiniteInnerPolynomialSmoothness NormTaylorRemainderBound NormJetUP NormJet
  RefinedJetRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [taylor_coefficient_adjacent_terms]: the coefficient sum
    of Federer 1.10.4, p. 46, for S_n with coefficients through degree
    n+1 has exactly the terms of degrees n and n+1; supporting 3.1.15,
    p. 228. *)
Lemma taylor_coefficient_adjacent_terms (K : fieldType) (V W : lmodType K) n
    (F : forall m, S_m V W m) (w : V) :
  taylor_coefficient n.+2 F n w=
    symmetric_taylor_term n (F n) w+symmetric_taylor_term n (F n.+1) w.
Proof.
rewrite /taylor_coefficient.
have -> : \sum_(m<n.+2 | (n<=m)%N) symmetric_taylor_term n (F m) w
    =\sum_(n<=m<n.+2) symmetric_taylor_term n (F m) w by rewrite big_geq_mkord.
by rewrite (big_nat_recr _ _ _ (leqnSn n)) big_nat1.
Qed.

(** Source for [polynomial_coefficient_translation_step]: for a
    polynomial of degree at most n+1, the translation identity of
    Federer 1.10.4, pp. 46–47, gives S_n(a+w)=S_n(a)+S_(n+1)(a)
    contracted with w, evaluated on an n-tuple; supporting 3.1.15,
    p. 228, for every n, including n=0. *)
Lemma polynomial_coefficient_translation_step (R : realType) (X Y : lmodType R)
    (P : PolynomialFunction X Y) n (hdeg : (polynomial_degree P<=n.+1)%N)
    (a w : X) (t : n.-tuple X) :
  polynomial_taylor_coefficient P n (a+w) t=
    polynomial_taylor_coefficient P n a t+
    polynomial_taylor_coefficient P n.+1 a
      (tcast (subnKC (leqnSn n)) [tuple of t++[tuple w | j<n.+1-n]]).
Proof.
have hfP : grade_bounded (S_star_grading X Y) (polynomial_to_forms P) n.+2.
  exact: (grade_bounded_mono (hdeg : ((polynomial_degree P).+1<=n.+2)%N)
    (@graded_degree_bound R _ (S_star_grading X Y) (polynomial_to_forms P))).
have hlt : (n<n.+2)%N by [].
rewrite {1}/polynomial_taylor_coefficient
  (symmetric_taylor_coefficient_translation (@pchar_num R) a w hfP hlt)
  taylor_coefficient_adjacent_terms sform_addE
  (symmetric_taylor_term_tuple_value (leqnn n))
  (symmetric_taylor_term_tuple_value (leqnSn n)).
have -> : (((n-n)`!)%:R : R)^-1= 1 by rewrite subnn fact0 invr1.
have -> : (((n.+1-n)`!)%:R : R)^-1= 1 by rewrite subSnn factS fact0 muln1 invr1.
by rewrite !scale1r cat_empty_tuple_cast.
Qed.

Section TopLaws.
Variable R : realType.
Variable m : nat.
Local Notation X := (R_n R m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable Y : lmodType R.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i).
Variable A : X->Prop.
Variable f : X->Y.
Variable K : nat.
Variable a : X.
Variable zz : Z K.+1.
Hypothesis hzz : has_norm_higher_differential NX ev ZN A f K.+1 a zz.
Variable P : PolynomialFunction X Y.
Hypothesis hP : is_norm_jet_polynomial NX ev ZN A f K.+1 a P.

(** Source for [jet_top_differential_fields]: the differentials of the
    (k+1)-jet P_a on the whole space are the coefficients S_i of 1.10.4,
    p. 46, by Federer 3.1.11, p. 221; at the base point they are the
    differentials of f, and the top one is D^(k+1)f(a). Supporting
    3.1.15, p. 228. *)
Lemma jet_top_differential_fields :
  exists DP : forall i, X->Z i,
    (forall i x u, @ev i u (DP i x)=
      polynomial_taylor_coefficient P i x [tuple u j | j<i]) /\
    (forall i x, has_norm_higher_differential NX ev ZN (fun _=>True) P i x (DP i x)) /\
    DP K.+1 a=zz /\
    (forall i, (i<=K.+1)%N -> has_norm_higher_differential NX ev ZN A f i a (DP i a)).
Proof.
have hAint x : (fun _ : X=>True) x -> norm_domain_interior NX (fun _=>True) x.
  by move=> _; exists 1; split; [exact: ltr01|move=> v _].
have [DP [hDPe hDPd]] := @finite_inner_polynomial_differential_fields R X Y _
  (@euclidean_inner_productP R m) NY hNY m _ (@coordinate_basisP R m) Z ev ZN hZ
  (fun _=>True) hAint P.
have [E [hE _]] := norm_jet_polynomial_expansion hP.
have hDPa i (hi : (i<=K.+1)%N) : DP i a=E i.
  exact: (norm_higher_differential_unique hNX hNY hZ (hDPd i a I)
    (norm_jet_differential_at_base hNX hNY hZ hP hi (hE i hi))).
exists DP; split; first exact: hDPe.
split; first by move=> i x; exact: (hDPd i x I).
split.
- rewrite (hDPa K.+1 (leqnn _)).
  exact: (norm_higher_differential_unique hNX hNY hZ (hE K.+1 (leqnn _)) hzz).
- by move=> i hi; rewrite (hDPa i hi); exact: (hE i hi).
Qed.

(** Source for [jet_top_differential_constant]: the (k+1)-st
    differential of the (k+1)-jet P_a is constant, equal to
    D^(k+1)f(a), as used in the computation of
    D^(k+1)P_a(b)-D^(k+1)P_b(b) in Federer 3.1.15, p. 228. The jet has
    degree at most k+1 by 3.1.11, p. 221, so S_(k+2) vanishes and the
    translation identity of 1.10.4, pp. 46–47, leaves S_(k+1) unchanged. *)
Theorem jet_top_differential_constant (b : X) (w : Z K.+1) :
  has_norm_higher_differential NX ev ZN (fun _=>True) P K.+1 b w -> w=zz.
Proof.
move=> hw.
have [DP [hDPe [hDPd [hDPz _]]]] := jet_top_differential_fields.
rewrite -hDPz -(norm_higher_differential_unique hNX hNY hZ (hDPd K.+1 b) hw).
apply: (continuous_multilinear_extensional (@hZ K.+1))=> u.
have hb : b=a+(b-a) by rewrite addrCA subrr addr0.
have hdeg : (polynomial_degree P<=K.+2)%N :=
  leq_trans (norm_jet_polynomial_degree hP) (leqnSn K.+1).
rewrite !hDPe {1}hb (polynomial_coefficient_successor_translation hdeg).
by rewrite (polynomial_taylor_coefficient_above_degree (@pchar_num R) a
  (norm_jet_polynomial_degree hP : (polynomial_degree P<K.+2)%N)) sform_zeroE addr0.
Qed.

(** Source for [jet_top_differential_affine]: the k-th differential of
    the (k+1)-jet P_a is affine, D^k P_a(a+h)=D^k f(a)+<h,D D^k f(a)>,
    as used in the computation of D^k P_a(b)-D^k P_b(b) in Federer
    3.1.15, p. 228. The jet has degree at most k+1 by 3.1.11, p. 221,
    and the translation identity of 1.10.4, pp. 46–47, gives
    S_k(a+h)=S_k(a)+S_(k+1)(a) contracted with h. *)
Theorem jet_top_differential_affine (zK : Z K) (L : Hom X (Z K)) (h : X) (w : Z K) :
  has_norm_higher_differential NX ev ZN A f K a zK ->
  (forall u v, @ev K u (L v)=@ev K.+1 (multilinear_successor_arguments u v) zz) ->
  has_norm_higher_differential NX ev ZN (fun _=>True) P K (a+h) w -> w=zK+L h.
Proof.
move=> hzK hL hw.
have [DP [hDPe [hDPd [hDPz hDPf]]]] := jet_top_differential_fields.
have hzKe : zK=DP K a.
  exact: (norm_higher_differential_unique hNX hNY hZ hzK (hDPf K (leqnSn K))).
rewrite hzKe -(norm_higher_differential_unique hNX hNY hZ (hDPd K (a+h)) hw).
apply: (continuous_multilinear_extensional (@hZ K))=> u.
rewrite raddfD /= hL -hDPz !hDPe.
by rewrite (polynomial_coefficient_translation_step (norm_jet_polynomial_degree hP))
  successor_arguments_tuple.
Qed.
End TopLaws.
