(** Federer (1969), 3.1.24, p. 239: the first
    symmetric derivative form is the ordinary differential,
    acting on a vector through its symmetric generator. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal.
From Federer Require Import Hom HomogeneousHom BoundedHom RealNormUP SymmetricAlgebra SymmetricForms
  SymmetricFormExtension SymmetricFormIsomorphism SymmetricFormWords SymmetricOperatorNorm SymmetricOperatorTupleBound
  ContinuousMultilinearUP ContinuousMultilinearOne NormDifferentialUP NormHigherDifferentialUP
  NormHigherDifferentialFirst NormHigherSymmetricFormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_first_derivative_map]: the linear
    map represented by the first symmetric derivative form,
    supporting Federer 3.1.24, p. 239. It is the
    form's homogeneous map composed with the symmetric generator. *)
Definition symmetric_first_derivative_map (K:fieldType) (X Y:lmodType K)
    (phi:S_m X Y 1):Hom X Y :=
  hom_comp (sform_homogeneous phi)
    (hom_of_linear (GRing.Linear.clone _ _ _ _ (@symmetric_generator K X) _)).

(** Source for [symmetric_first_derivative_mapE]: evaluation
    on the singleton tuple, supporting the first-order term
    in Federer 3.1.24, p. 239. *)
Lemma symmetric_first_derivative_mapE (K:fieldType) (X Y:lmodType K)
    (phi:S_m X Y 1) x : symmetric_first_derivative_map phi x=phi [tuple x].
Proof.
rewrite /symmetric_first_derivative_map hom_compE hom_of_linearE.
change (sform_homogeneous phi (symmetric_word [tuple x])=phi [tuple x]).
by rewrite sform_homogeneousE sform_extensionE sform_wordsE.
Qed.

(** Source for [symmetric_first_derivative_map_bound]: a finite
    first-form norm bound is a linear-map bound, supporting
    the inverse derivative majorant in Federer 3.1.24, p. 240. *)
Lemma symmetric_first_derivative_map_bound (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (phi:S_m X Y 1) C :
  (symmetric_operator_norm hNX.1 NY phi<=C%:E)%E ->
  forall x,NY (symmetric_first_derivative_map phi x)<=C*NX x.
Proof.
move=>hb x; rewrite symmetric_first_derivative_mapE.
have hh:=@symmetric_operator_finite_tuple_bound R X Y NX NY hNX hNY.1 1%N phi C hb [tuple x].
by rewrite big_ord1 tnth0 in hh.
Qed.

(** Source for [norm_first_form_map_actual]: an actual first
    symmetric differential form represents the actual ordinary
    differential, supporting the inverse identities in Federer
    3.1.24, p. 239, by the convention of 3.1.11,
    p. 219. Only abstract multilinear-space laws are used. *)
Lemma norm_first_form_map_actual (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->X}->Hom (Z i) Y)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A:X->Prop) (f:X->Y) a (phi:S_m X Y 1) :
  is_norm_higher_differential_form NX ev ZN A f 1 a phi ->
  has_norm_differential NX NY A f a (symmetric_first_derivative_map phi).
Proof.
move=>[z [hz he]].
have hd:=(@norm_higher_differential_first R X Y NX NY hNX hNY Z ev ZN hZ A f a z).1 hz.
have hMap:symmetric_first_derivative_map phi=
    @continuous_multilinear_one_operator R X Y (Z 1%N) NX NY (@ev 1%N) (@ZN 1%N) (hZ 1%N) z.
  apply:hom_ext=>v; rewrite symmetric_first_derivative_mapE.
  change (phi [tuple v]=ev 1%N [ffun i=>v] z).
  have hh:=he [ffun i:'I_1=>v].
  have ht:[tuple [ffun i:'I_1=>v] j | j<1]= [tuple v].
    apply:eq_from_tnth=>i; by rewrite (ord1 i) tnth0 tnth_mktuple ffunE.
  by rewrite ht in hh.
by rewrite hMap.
Qed.
