(** Federer (1969), 3.1.15, p. 228: the refined remainder estimate
    for the (s+2)-jet. If f is of class s+1 on A, the (s+2)-differential
    of f at a exists, and the (s+1)-differential field H satisfies
    ||H x-H a-L (x-a)||<=eta|x-a| on a ball about a, then f minus its
    (s+2)-jet at a is bounded by eta|v|^(s+2)/(s+1)! along every segment
    from a inside A. The argument applies the Taylor integral estimate
    of 3.1.11, pp. 220–221, to the difference f-P, whose (s+1)-field
    is H-D^(s+1)P, and uses the affine form of D^(s+1)P. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SymmetricForms SymmetricFormSum
  Graded GradedDegree PolynomialFunctions PolynomialRepresentations PolynomialTaylorTerms
  PolynomialTaylorCoefficients PolynomialTaylorTermContinuity PolynomialTaylorTransform
  PolynomialTaylor MultilinearSuccessorArguments MultilinearSuccessorPermutation
  ContinuousMultilinearUP ContinuousMultilinearNorm NormDifferentialUP NormClassOneUP
  NormClassZeroArithmetic NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherDifferentialLocal NormHigherDifferentialArithmetic NormClassHigherUP
  NormClassHigherFields NormClassHigherDerivative FiniteInnerPolynomialSmoothness
  NormTaylorRemainderBound NormJetUP NormJet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [nth_const_seq]: a supporting tuple identity for the
    contraction formula of Federer 1.10.4, p. 46, used in 3.1.15, p. 228:
    every entry of a constant family is the constant. *)
Lemma nth_const_seq (T : Type) (w : T) k i : nth w [seq w | _ <- enum 'I_k] i=w.
Proof.
case: (ltnP i k)=>hik.
- by rewrite (nth_map (Ordinal hik)) ?size_enum_ord.
- by rewrite nth_default // size_map size_enum_ord.
Qed.

(** Source for [cat_empty_tuple_cast]: the contraction with x^0/0!
    in Federer 1.10.4, p. 46, leaves the argument tuple unchanged;
    supporting 3.1.15, p. 228. *)
Lemma cat_empty_tuple_cast (T : Type) n (hn : (n<=n)%N) (t : n.-tuple T) (w : T) :
  tcast (subnKC hn) [tuple of t++[tuple w | j<n-n]]=t.
Proof.
by apply: eq_from_tnth=>j; rewrite tcastE !(tnth_nth w) /= nth_cat size_tuple ltn_ord.
Qed.

(** Source for [successor_arguments_tuple]: appending one vector to a
    family of n arguments, as in the recursive differential of Federer
    3.1.11, p. 219, is the tuple concatenation used by the contraction
    x^1/1! of 1.10.4, p. 46; supporting 3.1.15, p. 228. *)
Lemma successor_arguments_tuple (T : Type) n (hn : (n<=n.+1)%N)
    (u : {ffun 'I_n->T}) (w : T) :
  tcast (subnKC hn) [tuple of [tuple u j | j<n]++[tuple w | j<n.+1-n]]=
  [tuple multilinear_successor_arguments u w j | j<n.+1].
Proof.
apply: eq_from_tnth=>j; rewrite tcastE tnth_mktuple (tnth_nth w) /= nth_cat size_tuple.
case: (unliftP ord_max j)=>[i ->|->].
- rewrite multilinear_successor_lift lift_max card_ord ltn_ord.
  by rewrite (nth_map i) ?size_enum_ord // nth_ord_enum.
- by rewrite multilinear_successor_last /= card_ord ltnn subnn nth_const_seq.
Qed.

(** Source for [taylor_coefficient_two_terms]: the coefficient sum of
    Federer 1.10.4, p. 46, for S_(s+1) with coefficients through degree
    s+2 has exactly the terms of degrees s+1 and s+2; supporting
    3.1.15, p. 228. *)
Lemma taylor_coefficient_two_terms (K : fieldType) (V W : lmodType K) s
    (F : forall m, S_m V W m) (w : V) :
  taylor_coefficient s.+3 F s.+1 w=
    symmetric_taylor_term s.+1 (F s.+1) w+symmetric_taylor_term s.+1 (F s.+2) w.
Proof.
rewrite /taylor_coefficient.
have -> : \sum_(m<s.+3 | (s.+1<=m)%N) symmetric_taylor_term s.+1 (F m) w
    =\sum_(s.+1<=m<s.+3) symmetric_taylor_term s.+1 (F m) w by rewrite big_geq_mkord.
by rewrite (big_nat_recr _ _ _ (leqnSn s.+1)) big_nat1.
Qed.

(** Source for [polynomial_coefficient_successor_translation]: for a
    polynomial of degree at most s+2, the translation identity of Federer
    1.10.4, pp. 46–47, gives S_(s+1)(a+w)=S_(s+1)(a)+S_(s+2)(a) contracted
    with w, evaluated on an (s+1)-tuple; supporting 3.1.15, p. 228. *)
Lemma polynomial_coefficient_successor_translation (R : realType) (X Y : lmodType R)
    (P : PolynomialFunction X Y) s (hdeg : (polynomial_degree P<=s.+2)%N)
    (a w : X) (t : s.+1.-tuple X) :
  polynomial_taylor_coefficient P s.+1 (a+w) t=
    polynomial_taylor_coefficient P s.+1 a t+
    polynomial_taylor_coefficient P s.+2 a
      (tcast (subnKC (leqnSn s.+1)) [tuple of t++[tuple w | j<s.+2-s.+1]]).
Proof.
have hfP : grade_bounded (S_star_grading X Y) (polynomial_to_forms P) s.+3.
  exact: (grade_bounded_mono (hdeg : ((polynomial_degree P).+1<=s.+3)%N)
    (@graded_degree_bound R _ (S_star_grading X Y) (polynomial_to_forms P))).
have hlt : (s.+1<s.+3)%N by [].
rewrite {1}/polynomial_taylor_coefficient
  (symmetric_taylor_coefficient_translation (@pchar_num R) a w hfP hlt)
  taylor_coefficient_two_terms sform_addE
  (symmetric_taylor_term_tuple_value (leqnn s.+1))
  (symmetric_taylor_term_tuple_value (leqnSn s.+1)).
have -> : (((s.+1-s.+1)`!)%:R : R)^-1= 1 by rewrite subnn fact0 invr1.
have -> : (((s.+2-s.+1)`!)%:R : R)^-1= 1 by rewrite subSnn factS fact0 muln1 invr1.
by rewrite !scale1r cat_empty_tuple_cast.
Qed.

(** Source for [difference_rearrangement]: the rearrangement of the
    (s+1)-field difference of f-P in the proof of Federer 3.1.15,
    p. 228. *)
Lemma difference_rearrangement (R : realType) (Z : lmodType R) (h1 h0 p l : Z) :
  h1-(p+l)-(h0-p)=h1-h0-l.
Proof. by rewrite opprB addrA opprD addrA [h1-p-l+p]addrAC subrK addrAC. Qed.

Section RefinedRemainder.
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
Variable s : nat.
Hypothesis hf : norm_class_higher NX NY ev ZN A f s.+1.
Variable H : X->Z s.+1.
Hypothesis hH : forall x, A x -> has_norm_higher_differential NX ev ZN A f s.+1 x (H x).
Variable a : X.
Variable L : Hom X (Z s.+1).
Variable zz : Z s.+2.
Hypothesis hzz : has_norm_higher_differential NX ev ZN A f s.+2 a zz.
Hypothesis hL : forall u v, @ev s.+1 u (L v)=@ev s.+2 (multilinear_successor_arguments u v) zz.
Variables (eta r : R).
Hypothesis heta : 0<=eta.
Hypothesis hr : 0<r.
Hypothesis hrate : forall x, A x -> NX (x-a)<r -> @ZN s.+1 (H x-H a-L (x-a))<=eta*NX (x-a).

(** Source for [refined_jet_remainder]: the computation of Federer
    3.1.15, p. 228: if D^(s+1)f is differentiable at a with derivative
    L and remainder at most eta|x-a|, then f minus its (s+2)-jet at a is
    bounded by eta|v|^(s+2)/(s+1)! along segments inside the domain.
    The Taylor integral estimate of 3.1.11, pp. 220–221, is applied to
    f-P on the segment, with D^(s+1)P(a+w)=D^(s+1)P(a)+L(w). *)
Theorem refined_jet_remainder (P : PolynomialFunction X Y) :
  is_norm_jet_polynomial NX ev ZN A f s.+2 a P ->
  forall v, NX v<r -> (forall t : R, 0<=t<= 1 -> A (a+t*:v)) ->
  NY (f (a+v)-P (a+v))<=eta*(NX v)^+s.+2/((s.+1)`!)%:R.
Proof.
move=> hP v hv hseg.
have hZN : is_real_norm (@ZN s.+1) := continuous_multilinear_norm_is_norm hNY (@hZ s.+1).
have ha : A a.
  have h0 : 0<=(0:R)<= 1 by rewrite lexx ler01.
  by have := hseg 0 h0; rewrite scale0r addr0.
have hAint : forall x, A x -> norm_domain_interior NX A x.
  by move=> x hx; exact: (hf.1 x hx).1.
have [Df [hDf hDfc]] := norm_class_higher_fields hNX hNY hZ hf.
have [DP [hDPe hDPd]] := @finite_inner_polynomial_differential_fields R X Y _
  (@euclidean_inner_productP R m) NY hNY m _ (@coordinate_basisP R m) Z ev ZN hZ A hAint P.
have hDPc : norm_class_zero NX (@ZN s.+1) A (DP s.+1).
  have [_ [D' [hD'f hD'c]]] := @finite_inner_polynomial_smooth R X Y _
    (@euclidean_inner_productP R m) NY hNY m _ (@coordinate_basisP R m) Z ev ZN hZ A hAint P s.+1.
  apply: (norm_class_zero_domain_agreement _ hD'c)=> x hx.
  exact: (norm_higher_differential_unique hNX hNY hZ (hD'f x hx) (hDPd s.+1 x hx)).
have [E [hE hPe]] := norm_jet_polynomial_expansion hP.
have hEP i (hi : (i<=s.+2)%N) : has_norm_higher_differential NX ev ZN A P i a (E i).
  have hT := norm_jet_differential_at_base hNX hNY hZ hP hi (hE i hi).
  exact: (norm_higher_differential_open_restriction hNX hNY hZ (A:=fun _=>True) (O:=A)
    P (fun x _=>I) hAint ha (E i)).1 hT.
have hDPa i (hi : (i<=s.+2)%N) : DP i a=E i.
  exact: (norm_higher_differential_unique hNX hNY hZ (hDPd i a ha) (hEP i hi)).
have hDfa i (hi : (i<=s.+1)%N) : Df i a=E i.
  exact: (norm_higher_differential_unique hNX hNY hZ (hDf i hi a ha)
    (hE i (leq_trans hi (leqnSn _)))).
have hEz : E s.+2=zz.
  exact: (norm_higher_differential_unique hNX hNY hZ (hE s.+2 (leqnn _)) hzz).
have hHa x (hx : A x) : Df s.+1 x=H x.
  exact (norm_higher_differential_unique hNX hNY hZ (hDf s.+1 (leqnn s.+1) x hx) (hH hx)).
have haff w : DP s.+1 (a+w)=DP s.+1 a+L w.
  apply: (continuous_multilinear_extensional (@hZ s.+1))=> u.
  rewrite raddfD /= hL -hEz -(hDPa s.+2 (leqnn _)) !hDPe.
  by rewrite (polynomial_coefficient_successor_translation (norm_jet_polynomial_degree hP))
    successor_arguments_tuple.
pose D i x := Df i x-DP i x.
have hDE i x : D i x=Df i x-DP i x by [].
have hD : forall i, (i<=s.+1)%N -> forall x, A x ->
    has_norm_higher_differential NX ev ZN A (fun x=>f x-P x) i x (D i x).
  move=> i hi x hx.
  have hsc : forall y, A y ->
      has_norm_higher_differential NX ev ZN A (fun y=>(-1)*:P y) i y ((-1)*:DP i y).
    exact: (norm_higher_differential_field_scale hNX hNY hZ (-1) (hDPd i)).
  have hadd := norm_higher_differential_field_add hNX hNY hZ (hDf i hi) hsc hx.
  have -> : (fun x=>f x-P x)=(fun x=>f x+(-1)*:P x).
    by apply/funext=> y; rewrite scaleN1r.
  have -> : D i x=Df i x+(-1)*:DP i x by rewrite hDE scaleN1r.
  exact hadd.
have hc : norm_class_zero NX (@ZN s.+1) A (D s.+1).
  have hsum : norm_class_zero NX (@ZN s.+1) A (fun x=>Df s.+1 x+(-1)*:DP s.+1 x) :=
    norm_class_zero_add hZN (hDfc s.+1 (leqnn _)) (norm_class_zero_scale hZN (-1) hDPc).
  apply: (norm_class_zero_domain_agreement _ hsum)=> x _.
  by rewrite hDE scaleN1r.
have hw : forall t : R, 0<=t<= 1 -> @ZN s.+1 (D s.+1 (a+t*:v)-D s.+1 a)<=eta*NX v.
  move=> t /andP [ht0 ht1].
  have hat : A (a+t*:v) by apply: hseg; rewrite ht0 ht1.
  have hvv : a+t*:v-a=t*:v by rewrite addrAC subrr add0r.
  have hnt : NX (t*:v)=t*NX v by rewrite (real_seminorm_scale hNX.1) (ger0_norm ht0).
  have hle : t*NX v<=NX v := ler_piMl (real_seminorm_nonnegative hNX.1 v) ht1.
  have hsmall : NX (a+t*:v-a)<r by rewrite hvv hnt; exact: (le_lt_trans hle hv).
  have hb := hrate hat hsmall.
  rewrite hvv hnt in hb.
  have heq : D s.+1 (a+t*:v)-D s.+1 a=H (a+t*:v)-H a-L (t*:v).
    by rewrite !hDE haff (hHa _ hat) (hHa _ ha) difference_rearrangement.
  rewrite heq.
  exact: (le_trans hb (ler_wpM2l heta hle)).
have hb : NY (f (a+v)-P (a+v)-norm_taylor_value ev D a v s.+1)<=
    eta*NX v*(NX v)^+s.+1/((s.+1)`!)%:R :=
  norm_taylor_remainder_oscillation_bound hNX hNY hZ hD hc hseg hw.
have h0 : norm_taylor_value ev D a v s.+1= 0.
  rewrite /norm_taylor_value; apply: big1=> i _.
  have hi : (i<=s.+1)%N := ltn_ord i.
  by rewrite hDE (hDfa i hi) (hDPa i (leq_trans hi (leqnSn _))) subrr raddf0 scaler0.
rewrite h0 subr0 in hb.
by rewrite exprS mulrA.
Qed.
End RefinedRemainder.
