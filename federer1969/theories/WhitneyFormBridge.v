(** Federer (1969), 3.1.14, pp. 225–226:
    the global higher differentials of the polynomials P_a
    are represented by their Taylor coefficient forms, and the
    norms of representatives of coefficient differences are the
    symmetric operator norms entering rho(C,delta). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP SymmetricForms
  PolynomialFunctions PolynomialRepresentations PolynomialTaylor
  SymmetricOperatorNormUP SymmetricOperatorNorm ContinuousMultilinearUP
  ContinuousMultilinearSymmetricNorm NormDifferentialUP NormHigherDifferentialUP
  NormHigherDifferentialArithmetic NormClassHigherUP FiniteInnerPolynomialSmoothness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [sform_subE]:
    evaluation of a difference of symmetric forms,
    Federer 1.10.4, p. 46, supporting 3.1.14, p. 226. *)
Lemma sform_subE (K : fieldType) (V W : lmodType K) n (f g : S_m V W n) t : (f-g) t=f t-g t.
Proof. by rewrite -[-g]scaleN1r sform_addE sform_scaleE scaleN1r. Qed.
Section FormBridge.
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

(** Source for [whitney_whole_space_interior]:
    R^m is open in itself; the global differentials of
    Federer 3.1.14, p. 225, use the whole space as domain. *)
Lemma whitney_whole_space_interior : forall x : X, True -> norm_domain_interior N (fun _=>True) x.
Proof. move=>x _; exists 1; split; first exact: ltr01; by move=>u _. Qed.

(** Source for [whitney_polynomial_fields_exist]:
    a choice of representatives D^i Q of the global higher
    differentials of every polynomial Q, evaluating to its
    Taylor coefficient forms, Federer 3.1.11, p. 221, as used
    in 3.1.14, pp. 225–227. *)
Theorem whitney_polynomial_fields_exist :
  exists DP : PolynomialFunction (R_n R m) Y->forall i, X->Z i,
    (forall Q i x u, @ev i u (DP Q i x)=polynomial_taylor_coefficient Q i x [tuple u j | j<i]) /\
    forall (Q : PolynomialFunction (R_n R m) Y) i x,
      has_norm_higher_differential N ev ZN (fun _=>True) Q i x (DP Q i x).
Proof.
have hex (Q : PolynomialFunction (R_n R m) Y) : exists D : forall i, X->Z i,
    (forall i x u, @ev i u (D i x)=polynomial_taylor_coefficient Q i x [tuple u j | j<i]) /\
    forall i x, has_norm_higher_differential N ev ZN (fun _=>True) Q i x (D i x).
  have [D [hD hd]] := @finite_inner_polynomial_differential_fields R (R_n R m) Y _
    (@euclidean_inner_productP R m) NY hNY m _ (@coordinate_basisP R m) Z ev ZN hZ
    (fun _=>True) whitney_whole_space_interior Q.
  exists D; split; first exact hD.
  by move=>i x; exact: (hd i x I).
have [DP hDP] := choice hex.
exists DP; split=>[Q|Q]; [exact: (hDP Q).1|exact: (hDP Q).2].
Qed.

Variable DP : PolynomialFunction (R_n R m) Y->forall i, X->Z i.
Hypothesis hDP : forall Q i x u, @ev i u (DP Q i x)=polynomial_taylor_coefficient Q i x [tuple u j | j<i].
Hypothesis hDPd : forall (Q : PolynomialFunction (R_n R m) Y) i x,
  has_norm_higher_differential N ev ZN (fun _=>True) Q i x (DP Q i x).

(** Source for [whitney_coefficient_difference_evaluation]:
    the difference of two representatives evaluates to the
    difference of the coefficient forms, Federer 3.1.14, p. 226. *)
Lemma whitney_coefficient_difference_evaluation (Q Q' : PolynomialFunction (R_n R m) Y) i x u :
  @ev i u (DP Q i x-DP Q' i x)=
    (polynomial_taylor_coefficient Q i x-polynomial_taylor_coefficient Q' i x) [tuple u j | j<i].
Proof. by rewrite sform_subE -!hDP -raddfB. Qed.

(** Source for [whitney_coefficient_difference_norm]:
    ||D^i Q(x)-D^i Q'(x)|| is the symmetric operator norm of
    the coefficient difference, Federer 3.1.14, p. 226, with the
    norm identification of 3.1.11, p. 219. *)
Lemma whitney_coefficient_difference_norm (Q Q' : PolynomialFunction (R_n R m) Y) i x :
  symmetric_operator_norm hN.1 NY
    (polynomial_taylor_coefficient Q i x-polynomial_taylor_coefficient Q' i x)=
  (@ZN i (DP Q i x-DP Q' i x))%:E.
Proof.
apply: (continuous_multilinear_symmetric_norm hN hNY (@hZ i))=>t.
rewrite whitney_coefficient_difference_evaluation; congr (_ _).
by apply: eq_from_tnth=>l; rewrite tnth_mktuple ffunE.
Qed.

(** Source for [whitney_coefficient_difference_bound]:
    a real bound on the operator norm of a coefficient difference
    is a bound on the norm of the representative difference,
    Federer 3.1.14, p. 226. *)
Lemma whitney_coefficient_difference_bound (Q Q' : PolynomialFunction (R_n R m) Y) i x (L : R) :
  (symmetric_operator_norm hN.1 NY
    (polynomial_taylor_coefficient Q i x-polynomial_taylor_coefficient Q' i x)%R<=L%:E)%E ->
  @ZN i (DP Q i x-DP Q' i x)<=L.
Proof. by rewrite whitney_coefficient_difference_norm lee_fin. Qed.

(** Source for [whitney_polynomial_difference_field]:
    the representatives of the global higher differentials of
    Q-Q' are the differences of the representatives,
    Federer 3.1.11, p. 221, and 3.1.14, p. 226. *)
Lemma whitney_polynomial_difference_field (Q Q' : PolynomialFunction (R_n R m) Y) i x :
  has_norm_higher_differential N ev ZN (fun _=>True) (fun y : X=>Q y-Q' y) i x
    (DP Q i x-DP Q' i x).
Proof.
have hscale : forall y, True -> has_norm_higher_differential N ev ZN (fun _=>True)
    (fun y : X=>(-1)*:Q' y) i y ((-1)*:DP Q' i y).
  apply: (norm_higher_differential_field_scale hN hNY hZ (A:=fun _=>True) (D:=DP Q' i))=>y _.
  exact: hDPd.
have hadd := norm_higher_differential_field_add hN hNY hZ (A:=fun _=>True) (D:=DP Q i)
  (E:=fun y=>(-1)*:DP Q' i y) (fun y _=>hDPd Q i y) hscale (x:=x) I.
have -> : (fun y : X=>Q y-Q' y)=(fun y : X=>Q y+(-1)*:Q' y).
  by apply/funext=>y; rewrite scaleN1r.
have -> : DP Q i x-DP Q' i x=DP Q i x+(-1)*:DP Q' i x by rewrite scaleN1r.
exact hadd.
Qed.
End FormBridge.
