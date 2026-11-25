(** Federer (1969), 3.1.11, pp. 218–219:
    the first higher differential agrees with the ordinary
    differential. The abstract one-linear space is identified
    isometrically with the continuous operator space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP TensorFamilyUP FamilyUpdate
  ContinuousMultilinearUP NormDifferentialUP NormOperatorNormUP ContinuousOperatorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [one_arity_arguments]: the one argument
    family in "once differentiable", Federer 3.1.11,
    p. 219. *)
Lemma one_arity_arguments (X : Type) (u : {ffun 'I_1->X}) :
  u=[ffun i=>u ord0].
Proof. by apply/ffunP=> i; rewrite ffunE (ord1 i). Qed.

(** Source for [one_arity_replace]: replacing the unique
    argument of a one-linear form, supporting its identification
    with a linear map in Federer 3.1.11, p. 219. *)
Lemma one_arity_replace (X : Type) (u : {ffun 'I_1->X}) (x : X) :
  @family_with 1 (fun _ : 'I_1=>X) u ord0 x=[ffun i=>x].
Proof. by apply/ffunP=> i; rewrite (ord1 i) family_with_in ffunE. Qed.

Section OneForms.
Variable R : realType.
Variables X Y Z : lmodType R.
Variables NX : X->R.
Variable NY : Y->R.
Variable evaluation : {ffun 'I_1->X}->Hom Z Y.
Variable ZN : Z->R.
Hypothesis hZ : is_continuous_multilinear_space NX NY evaluation ZN.

(** Source for [continuous_multilinear_one_linear]: one-linear
    evaluation is linear in the unique argument, Federer
    3.1.11, p. 219. *)
Lemma continuous_multilinear_one_linear z : linear (fun x : X=>evaluation [ffun i=>x] z).
Proof.
move=> c x y.
have hf := continuous_multilinear_evaluation hZ z.
have hh := @hf [ffun i : 'I_1=>(0:X)] ord0 c x y.
by rewrite !one_arity_replace in hh.
Qed.

(** Source for [continuous_multilinear_one_operator]: the
    ordinary linear map corresponding to a one-linear form
    in Federer 3.1.11, p. 219. *)
Definition continuous_multilinear_one_operator z : Hom X Y :=
  @HomMap R X Y (fun x=>evaluation [ffun i=>x] z)
    (introT (asboolP _) (continuous_multilinear_one_linear z)).

(** Source for [continuous_multilinear_one_operator_linear]:
    the identification with ordinary operators is linear,
    supporting Federer 3.1.11, p. 219. *)
Lemma continuous_multilinear_one_operator_linear : linear continuous_multilinear_one_operator.
Proof.
move=> c z w; apply: hom_ext=> x.
change (evaluation [ffun i=>x] (c*:z+w)=
  c*:evaluation [ffun i=>x] z+evaluation [ffun i=>x] w).
by rewrite linearP.
Qed.

(** Source for [continuous_multilinear_one_evaluation]: the
    linear evaluation map into ordinary operators, supporting
    the first-order convention of Federer 3.1.11, p. 219. *)
Definition continuous_multilinear_one_evaluation : Hom Z (Hom X Y) :=
  @HomMap R Z (Hom X Y) continuous_multilinear_one_operator
    (introT (asboolP _) continuous_multilinear_one_operator_linear).

(** Source for [continuous_multilinear_one_norm_laws]:
    the one-linear norm is exactly the ordinary operator norm,
    Federer 3.1.11, p. 219, corrected by erratum
    p. 4, book p. 219 line 4. *)
Lemma continuous_multilinear_one_norm_laws z :
  is_norm_operator_norm NX NY (continuous_multilinear_one_operator z) (ZN z).
Proof.
constructor.
- exact: multilinear_operator_nonnegative (continuous_multilinear_norm_laws hZ z).
- move=> x; have hh := multilinear_operator_bound
    (continuous_multilinear_norm_laws hZ z) [ffun i : 'I_1=>x].
  by rewrite big_ord1 ffunE in hh.
- move=> C hC hb.
  apply: (multilinear_operator_least (continuous_multilinear_norm_laws hZ z) hC)=> u.
  have hh := hb (u ord0).
  change (is_true (NY (evaluation [ffun i=>u ord0] z)<=C*NX (u ord0))) in hh.
  by rewrite (one_arity_arguments u) big_ord1 !ffunE.
Qed.

(** Source for [continuous_multilinear_one_operator_space]:
    the one-linear space satisfies all laws of the space
    of continuous linear maps used in 3.1.1, pp. 210–211,
    as required by "once differentiable" in 3.1.11, p. 219. *)
Theorem continuous_multilinear_one_operator_space :
  is_continuous_operator_space NX NY continuous_multilinear_one_evaluation ZN.
Proof.
constructor.
- move=> z w he; apply: (continuous_multilinear_extensional hZ)=> u.
  have hh := congr1 (fun L : Hom X Y=>L (u ord0)) he.
  by rewrite (one_arity_arguments u).
- move=> z; exists (ZN z); split.
  + exact: norm_operator_nonnegative (continuous_multilinear_one_norm_laws z).
  + exact: norm_operator_bound (continuous_multilinear_one_norm_laws z).
- move=> L [C [hC hb]].
  have hf : norm_bounded_multilinear NX NY (fun u : {ffun 'I_1->X}=>L (u ord0)).
    split.
    + move=> u i c x y; rewrite (ord1 i).
      by rewrite !family_with_in linearP.
    + exists C; split=> // u; rewrite big_ord1; exact: hb.
  have [z hz] := continuous_multilinear_surjective hZ hf.
  exists z; apply: hom_ext=> x.
  have hh := hz [ffun i : 'I_1=>x]; by rewrite ffunE in hh.
- exact: continuous_multilinear_one_norm_laws.
Qed.
End OneForms.
