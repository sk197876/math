(** Federer (1969), 3.1.11, pp. 219–221:
    the continuous symmetric coefficient forms are
    represented in the abstract multilinear spaces.
    The tuple interface from Chapter 1 is retained. *)
From mathcomp Require Import all_boot all_order all_algebra perm boolp reals constructive_ereal.
From Federer Require Import Hom RealNormUP TensorFamilyUP PowerWords
  SymmetricForms SymmetricFormWords SymmetricFormPermutations
  SymmetricOperatorNorm SymmetricOperatorTupleBound
  ContinuousMultilinearUP FiniteArgumentPermutation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_bounded_symmetric_form]:
    continuity of the symmetric polynomial coefficient
    in Federer 3.1.11, p. 221,
    expressed by its finite homogeneous product
    bound from 1.10.5, p. 47. *)
Definition norm_bounded_symmetric_form (R : realType) k
    (X Y : lmodType R) (NX : X->R) (NY : Y->R) (phi : S_m X Y k) :=
  exists C : R, 0<=C /\ forall t : k.-tuple X,
    NY (phi t)<=C*\prod_(i<k) NX (tnth t i).

(** Source for [sform_finite_family_multilinear]:
    the tuple symmetric forms of 1.10.1,
    pp. 43–44, are multilinear in the
    finite-family interface used in 3.1.11, p. 219. *)
Lemma sform_finite_family_multilinear (K : fieldType) k
    (X Y : lmodType K) (phi : S_m X Y k) :
  multilinear (fun u : {ffun 'I_k->X}=>phi [tuple u i | i<k]).
Proof.
have he : (fun u : {ffun 'I_k->X}=>sform_words phi (power_seq u))=
    (fun u : {ffun 'I_k->X}=>phi [tuple u i | i<k]).
  apply: funext=>u; change (sform_words phi [tuple u i | i<k]=phi [tuple u i | i<k]).
  exact: sform_wordsE.
rewrite -he; exact: multilinear_words_power (sform_words_multilinear phi).
Qed.

(** Source for [sform_finite_family_symmetric]:
    permutation invariance is unchanged by the
    argument representation, Federer 3.1.11,
    p. 220, and 1.10.1, pp. 43–44. *)
Lemma sform_finite_family_symmetric (K : fieldType) k
    (X Y : lmodType K) (phi : S_m X Y k) s u :
  phi [tuple finite_argument_permutation s u i | i<k]=phi [tuple u i | i<k].
Proof.
have hh := sform_permutation phi [tuple u i | i<k] s.
have he : [tuple tnth [tuple u j | j<k] (s i) | i<k]=
    [tuple finite_argument_permutation s u i | i<k].
  apply: eq_from_tnth=>i.
  by rewrite !tnth_mktuple /finite_argument_permutation ffunE.
by rewrite he in hh.
Qed.

(** Source for [bounded_sform_finite_family]:
    the finite norm bound gives the continuous
    multilinear object required in Federer 3.1.11,
    pp. 219–221, including degree zero. *)
Lemma bounded_sform_finite_family (R : realType) k
    (X Y : lmodType R) (NX : X->R) (NY : Y->R) (phi : S_m X Y k) :
  norm_bounded_symmetric_form NX NY phi ->
  norm_bounded_multilinear NX NY (fun u : {ffun 'I_k->X}=>phi [tuple u i | i<k]).
Proof.
move=>[C [hC hb]]; split; first exact: sform_finite_family_multilinear.
exists C; split; first exact hC.
move=>u; have hh := hb [tuple u i | i<k].
have he : (\prod_(i<k) NX (tnth [tuple u j | j<k] i))=\prod_(i<k) NX (u i).
  apply: eq_bigr=>i _; by rewrite tnth_mktuple.
by rewrite he in hh.
Qed.

(** Source for [finite_operator_norm_sform_bounded]:
    a finite bound on the Chapter 1
    symmetric operator norm supplies the product
    bound for 3.1.11, p. 221,
    using 1.10.5, p. 47. *)
Lemma finite_operator_norm_sform_bounded (R : realType) k
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (phi : S_m X Y k) C :
  (symmetric_operator_norm hNX.1 NY phi<=C%:E)%E ->
  norm_bounded_symmetric_form NX NY phi.
Proof.
move=>hC.
have hn := le_trans (symmetric_operator_norm_ge_zero hNX.1 hNY.1 phi) hC.
have hC0 : 0<=C by move:hn; rewrite lee_fin.
exists C; split; first exact hC0.
exact (@symmetric_operator_finite_tuple_bound R X Y NX NY hNX hNY.1 k phi C hC).
Qed.

(** Source for [continuous_symmetric_form_representation]:
    a continuous symmetric form of Chapter 1
    has a unique evaluation representative in
    the abstract multilinear space of Federer
    3.1.11, p. 219. *)
Theorem continuous_symmetric_form_representation (R : realType) k
    (X Y Z : lmodType R) (NX : X->R) (NY : Y->R)
    (ev : {ffun 'I_k->X}->Hom Z Y) (ZN : Z->R)
    (hZ : is_continuous_multilinear_space NX NY ev ZN) (phi : S_m X Y k) :
  norm_bounded_symmetric_form NX NY phi ->
  exists z : Z, forall u, ev u z=phi [tuple u i | i<k].
Proof.
move=>hphi; exact (continuous_multilinear_surjective hZ (bounded_sform_finite_family hphi)).
Qed.

(** Source for [norm_bounded_symmetric_form_zero]:
    the zero coefficient is continuous,
    including the above-degree coefficients of
    Federer 3.1.11, p. 221. *)
Lemma norm_bounded_symmetric_form_zero (R : realType) k
    (X Y : lmodType R) (NX : X->R) (NY : Y->R) (hNY : is_real_norm NY) :
  norm_bounded_symmetric_form NX NY (0 : S_m X Y k).
Proof.
exists 0; split; first exact: lexx.
by move=>t; rewrite sform_zeroE (real_seminorm_zero hNY.1) mul0r.
Qed.

(** Source for [norm_bounded_symmetric_form_add]:
    finite coefficient addition preserves continuity,
    supporting the translated forms S_i in
    Federer 3.1.11, p. 221. *)
Lemma norm_bounded_symmetric_form_add (R : realType) k
    (X Y : lmodType R) (NX : X->R) (NY : Y->R) (hNY : is_real_norm NY)
    (phi psi : S_m X Y k) :
  norm_bounded_symmetric_form NX NY phi ->
  norm_bounded_symmetric_form NX NY psi ->
  norm_bounded_symmetric_form NX NY (phi+psi).
Proof.
move=>[C [hC hc]] [D [hD hd]].
exists (C+D); split; first exact: addr_ge0 hC hD.
move=>t; rewrite sform_addE mulrDl.
exact: le_trans (real_seminorm_triangle hNY.1 _ _) (lerD (hc t) (hd t)).
Qed.

(** Source for [norm_bounded_symmetric_form_scale]:
    constant scalar multiples of continuous forms
    are continuous, supporting the divided coefficients
    in Federer 3.1.11, p. 221. *)
Lemma norm_bounded_symmetric_form_scale (R : realType) k
    (X Y : lmodType R) (NX : X->R) (NY : Y->R) (hNY : is_real_norm NY)
    (phi : S_m X Y k) (a : R) :
  norm_bounded_symmetric_form NX NY phi ->
  norm_bounded_symmetric_form NX NY (a*:phi).
Proof.
move=>[C [hC hc]].
exists (`|a|*C); split; first exact: mulr_ge0 (normr_ge0 a) hC.
move=>t; rewrite sform_scaleE (real_seminorm_scale hNY.1) -mulrA.
exact (ler_wpM2l (normr_ge0 a) (hc t)).
Qed.
