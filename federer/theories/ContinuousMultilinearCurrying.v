(** Federer (1969), 3.1.11, pp. 218–219:
    currying a continuous (k+1)-linear form into a continuous
    linear map with values in the abstract k-linear space.
    Existence and uniqueness follow from its defining laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom RealNormUP TensorFamilyUP FamilyUpdate
  NormDifferentialUP NormOperatorNormUP ContinuousMultilinearUP
  ContinuousMultilinearOne MultilinearArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Currying.
Variable R : realType.
Variable k : nat.
Variables X Y Z : lmodType R.
Variable NX : X->R.
Variable NY : Y->R.
Variable evaluation : {ffun 'I_k->X}->Hom Z Y.
Variable ZN : Z->R.
Hypothesis hNX : is_real_norm NX.
Hypothesis hZ : is_continuous_multilinear_space NX NY evaluation ZN.

(** Source for [continuous_multilinear_curry_exists]:
    a (k+1)-linear map may be regarded as a linear map
    into the normed space of k-linear maps, as used to
    differentiate recursively in Federer 3.1.11, p. 219.
    Both spaces are arbitrary normed spaces, and k may be zero. *)
Theorem continuous_multilinear_curry_exists (f : {ffun 'I_(k+1)->X}->Y) :
  norm_bounded_multilinear NX NY f ->
  exists L : Hom X Z, norm_bounded_linear NX ZN L /\
    forall u x, evaluation u (L x)=f (multilinear_arguments_join u [ffun i : 'I_1=>x]).
Proof.
move=> [hf [C [hC hb]]].
have hfx x : norm_bounded_multilinear NX NY
    (fun u=>f (multilinear_arguments_join u [ffun i : 'I_1=>x])).
  split; first exact: multilinear_arguments_fixed_right hf _.
  exists (C*NX x); split.
  - exact: mulr_ge0 hC (real_seminorm_nonnegative hNX.1 _).
  - move=> u.
    have hh := hb (multilinear_arguments_join u [ffun i : 'I_1=>x]).
    rewrite multilinear_arguments_product big_ord1 ffunE in hh.
    have he : C*((\prod_(i<k) NX (u i))*NX x)=(C*NX x)*(\prod_(i<k) NX (u i)) by ring.
    by rewrite he in hh.
have hex x := continuous_multilinear_surjective hZ (hfx x).
pose g x := sval (constructive_indefinite_description (hex x)).
have hg x u : evaluation u (g x)=f (multilinear_arguments_join u [ffun i : 'I_1=>x]) :=
  svalP (constructive_indefinite_description (hex x)) u.
have hlin : linear g.
  move=> c x y; apply: (continuous_multilinear_extensional hZ)=> u.
  rewrite linearP /= !hg.
  have hm := multilinear_arguments_fixed_left hf u.
  have hh := @hm [ffun i : 'I_1=>(0:X)] ord0 c x y.
  rewrite !one_arity_replace in hh.
  exact hh.
pose L := @HomMap R X Z g (introT (asboolP _) hlin).
exists L; split; last by move=> u x; exact: (hg x u).
exists C; split=> // x.
apply: (multilinear_operator_least (continuous_multilinear_norm_laws hZ (L x))).
- exact: mulr_ge0 hC (real_seminorm_nonnegative hNX.1 _).
- move=> u; rewrite /L /= hg.
  have hh := hb (multilinear_arguments_join u [ffun i : 'I_1=>x]).
  rewrite multilinear_arguments_product big_ord1 ffunE in hh.
  have he : C*((\prod_(i<k) NX (u i))*NX x)=(C*NX x)*(\prod_(i<k) NX (u i)) by ring.
  by rewrite he in hh.
Qed.

(** Source for [continuous_multilinear_curry_unique]:
    the curried linear map is determined by evaluation,
    supporting the recursive interpretation of D^(k+1)f
    in Federer 3.1.11, p. 219. *)
Lemma continuous_multilinear_curry_unique
    (f : {ffun 'I_(k+1)->X}->Y) (L M : Hom X Z) :
  (forall u x, evaluation u (L x)=f (multilinear_arguments_join u [ffun i : 'I_1=>x])) ->
  (forall u x, evaluation u (M x)=f (multilinear_arguments_join u [ffun i : 'I_1=>x])) ->
  L=M.
Proof.
move=> hL hM; apply: hom_ext=> x.
apply: (continuous_multilinear_extensional hZ)=> u.
by rewrite hL hM.
Qed.

(** Source for [continuous_multilinear_curry_norm]:
    currying preserves the corrected multilinear norm of
    Federer 3.1.11, p. 219, erratum p. 4,
    book p. 219 line 4. No unit-vector maximizer is assumed. *)
Theorem continuous_multilinear_curry_norm
    (f : {ffun 'I_(k+1)->X}->Y) (c : R) (L : Hom X Z) :
  is_multilinear_operator_norm NX NY f c ->
  (forall u x, evaluation u (L x)=f (multilinear_arguments_join u [ffun i : 'I_1=>x])) ->
  is_norm_operator_norm NX ZN L c.
Proof.
move=> hf he; constructor.
- exact: multilinear_operator_nonnegative hf.
- move=> x.
  apply: (multilinear_operator_least (continuous_multilinear_norm_laws hZ (L x))).
  + exact: mulr_ge0 (multilinear_operator_nonnegative hf)
      (real_seminorm_nonnegative hNX.1 _).
  + move=> u; rewrite he.
    have hh := multilinear_operator_bound hf
      (multilinear_arguments_join u [ffun i : 'I_1=>x]).
    rewrite multilinear_arguments_product big_ord1 ffunE in hh.
    have heq : c*((\prod_(i<k) NX (u i))*NX x)=(c*NX x)*(\prod_(i<k) NX (u i)) by ring.
    by rewrite heq in hh.
- move=> C hC hb; apply: (multilinear_operator_least hf hC)=> w.
  pose u := multilinear_arguments_left w.
  pose x := w (rshift k ord0).
  have hw : w=multilinear_arguments_join u [ffun i : 'I_1=>x].
    rewrite -[LHS](multilinear_arguments_join_split w); congr multilinear_arguments_join.
    by apply/ffunP=> i; rewrite /multilinear_arguments_right !ffunE (ord1 i).
  rewrite hw -he multilinear_arguments_product big_ord1 ffunE.
  have h := multilinear_operator_bound (continuous_multilinear_norm_laws hZ (L x)) u.
  have hp : 0<=\prod_(i<k) NX (u i).
    apply: prodr_ge0=> i _; exact: (real_seminorm_nonnegative hNX.1 (u i)).
  apply: le_trans h _.
  have hh := ler_wpM2r hp (hb x).
  have heq : (C*NX x)*(\prod_(i<k) NX (u i))=
    C*((\prod_(i<k) NX (u i))*NX x) by ring.
  by rewrite heq in hh.
Qed.
End Currying.
