(** Private existence proof for the kth jet in
    Federer (1969), 3.1.11, p. 221.
    Actual differential coefficients are represented in
    the Chapter 1 symmetric algebra, then translated
    to the base point. The construction is hidden
    behind the jet specification and its seal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal.
From Federer Require Import Hom BoundedHom Graded GradedSums GradedDegree RealNormUP
  SymmetricForms SymmetricFormSum HomogeneousPolynomialFunctions PolynomialDiagonalNorm
  SymmetricPolynomialEvaluation PolynomialFunctions PolynomialRepresentations
  PolynomialTaylor PolynomialTaylorTransform
  ContinuousMultilinearUP ContinuousSymmetricFormAdapter
  NormHigherDifferentialUP NormHigherDifferentialLower NormHigherDifferentialSymmetricForm
  NormTaylorRemainderBound PolynomialTaylorCoefficientContinuity NormJetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_jet_polynomial_exists]:
    existence of the kth jet F_a,
    Federer 3.1.11, p. 221.
    Only k-fold differentiability at a is
    required. The resulting degree-at-most-k
    polynomial has continuous coefficient forms. *)
Theorem norm_jet_polynomial_exists (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) k a (z : Z k) :
  has_norm_higher_differential NX ev ZN A f k a z ->
  exists P : PolynomialFunction X Y,
    is_norm_jet_polynomial NX ev ZN A f k a P /\
    forall i, norm_bounded_symmetric_form NX NY
      (sform_component i (polynomial_to_forms P)).
Proof.
move=>hz.
have [D hD] := norm_higher_differential_point_family_exists hNX hz.
have hex i : exists phi : S_m X Y i,
    norm_bounded_symmetric_form NX NY phi /\
    ((i<=k)%N -> forall t, phi t=@ev i [ffun j=>tnth t j] (D i)).
  case hi:(i<=k)%N.
  - have [phi [he hn]] := norm_higher_differential_symmetric_form_exists hNX hNY hZ (hD i hi).
    exists phi; split; last by move=>_; exact he.
    apply: (@finite_operator_norm_sform_bounded R i X Y NX NY hNX hNY phi (@ZN i (D i))).
    by rewrite hn.
  - exists 0; split; first exact: norm_bounded_symmetric_form_zero hNY.
    by [].
pose phi i := projT1 (cid (hex i)).
have hphi i := projT2 (cid (hex i)).
pose F : S_star X Y := \sum_(i<k.+1) sform_include (phi i).
have hF : grade_bounded (S_star_grading X Y) F k.+1.
  exact: sform_finite_sum_bound.
pose P0 := polynomial_from_forms F.
have hP0degree : (polynomial_degree P0<=k)%N.
  rewrite /P0 (polynomial_degree_from_forms (@pchar_num R)).
  exact: graded_degree_le_of_bound hF.
have hP0 m (hm : (m<(polynomial_degree P0).+1)%N) :
    norm_bounded_symmetric_form NX NY (sform_component m (polynomial_to_forms P0)).
  have hmk : (m<k.+1)%N.
    rewrite ltnS; apply: leq_trans _ hP0degree.
    by move:hm; rewrite ltnS.
  rewrite /P0 (polynomial_from_formsK (@pchar_num R)) /F
    (sform_finite_sum_component phi hmk).
  exact: (hphi m).1.
pose P := polynomial_from_forms (symmetric_taylor_transform F (-a)).
exists P; split.
- constructor.
  + rewrite /P (polynomial_degree_from_forms (@pchar_num R)).
    apply: graded_degree_le_of_bound.
    exact (symmetric_taylor_transform_bound (@pchar_num R) (-a) hF).
  + exists D; split; first exact hD.
    move=>x; rewrite /P polynomial_from_formsE
      (symmetric_taylor_transform_value (@pchar_num R)) /F
      symmetric_polynomial_value_sum /norm_taylor_value.
    apply: eq_bigr=>i _.
    have hi : (i<=k)%N by move:(ltn_ord i); rewrite ltnS.
    rewrite symmetric_polynomial_value_include sform_polynomial_diagonal_value
      ((hphi i).2 hi).
    congr (_*:@ev i _ (D i)); apply/ffunP=>j.
    by rewrite !ffunE tnth_mktuple addrC.
- move=>i.
  have hb := @polynomial_taylor_coefficient_bounded R X Y NX NY hNX hNY
    P0 i (-a) hP0.
  rewrite /polynomial_taylor_coefficient /P0
    (polynomial_from_formsK (@pchar_num R)) in hb.
  by rewrite /P (polynomial_from_formsK (@pchar_num R)).
Qed.
