(** Federer (1969), 3.1.11, p. 221:
    all translated coefficient forms S_i(x)
    are continuous, including the zero coefficients
    above the polynomial's degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP SymmetricForms SymmetricFormSum
  PolynomialFunctions PolynomialRepresentations PolynomialTaylorCoefficients
  PolynomialTaylor ContinuousMultilinearUP ContinuousSymmetricFormAdapter
  PolynomialTaylorTermContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [taylor_coefficient_bounded]:
    the finite contraction sum S_i(x) from
    1.10.4, p. 46, consists of
    continuous forms when the original coefficients
    are continuous, as used in Federer 3.1.11, p. 221. *)
Theorem taylor_coefficient_bounded (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    N (phi : forall m, S_m X Y m) i x :
  (forall m, (m<N)%N -> norm_bounded_symmetric_form NX NY (phi m)) ->
  norm_bounded_symmetric_form NX NY (taylor_coefficient N phi i x).
Proof.
move=>hphi; rewrite /taylor_coefficient.
elim/big_ind: _=>[|p q hp hq|m hm].
- exact: norm_bounded_symmetric_form_zero hNY.
- exact (norm_bounded_symmetric_form_add hNY hp hq).
- exact: (@symmetric_taylor_term_bounded R X Y NX NY hNX hNY
    m i (phi m) x (hphi m (ltn_ord m))).
Qed.

(** Source for [polynomial_taylor_coefficient_bounded]:
    the intrinsic translated coefficient S_i(x)
    is continuous, supporting D^i P=S_i
    in Federer 3.1.11, p. 221. *)
Theorem polynomial_taylor_coefficient_bounded (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (P : PolynomialFunction X Y) i x :
  (forall m, (m<(polynomial_degree P).+1)%N ->
    norm_bounded_symmetric_form NX NY (sform_component m (polynomial_to_forms P))) ->
  norm_bounded_symmetric_form NX NY (polynomial_taylor_coefficient P i x).
Proof.
move=>hP; rewrite (polynomial_taylor_coefficient_formula (@pchar_num R)).
exact (@taylor_coefficient_bounded R X Y NX NY hNX hNY (polynomial_degree P).+1
  (fun m=>sform_component m (polynomial_to_forms P)) i x hP).
Qed.

(** Source for [polynomial_taylor_continuous_representatives]:
    the translated coefficient forms have exact
    representatives in the abstract multilinear spaces
    of Federer 3.1.11, p. 219,
    preparing their identification with D^i P
    on p. 221. Existence follows
    from the public representation laws. *)
Theorem polynomial_taylor_continuous_representatives (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (P : PolynomialFunction X Y) :
  (forall m, (m<(polynomial_degree P).+1)%N ->
    norm_bounded_symmetric_form NX NY (sform_component m (polynomial_to_forms P))) ->
  exists D : forall i, X->Z i,
    forall i x u, @ev i u (D i x)=
      polynomial_taylor_coefficient P i x [tuple u j | j<i].
Proof.
move=>hP.
have hex i x := @continuous_symmetric_form_representation R i X Y (Z i) NX NY
  (@ev i) (@ZN i) (@hZ i) (polynomial_taylor_coefficient P i x)
  (@polynomial_taylor_coefficient_bounded R X Y NX NY hNX hNY P i x hP).
pose D i x := projT1 (cid (hex i x)).
exists D=>i x u; exact: projT2 (cid (hex i x)) u.
Qed.
