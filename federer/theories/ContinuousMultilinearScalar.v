(** Federer (1969), 3.1.11, p. 220:
    for a real one-dimensional source, a continuous
    k-linear map is determined by its value on k copies
    of one. Its value on a tuple is the scalar product
    of the arguments times this coefficient. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP TensorFamilyUP FamilyUpdate
  MultilinearFamilyAlgebra ContinuousMultilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_family_product_replace]:
    a supporting product identity for the real-source
    identification in Federer 3.1.11, p. 220.
    Only the replaced scalar factor varies. *)
Lemma scalar_family_product_replace (R : realType) k
    (u : {ffun 'I_k->R^o}) (i : 'I_k) (t : R^o) :
  \prod_(j<k) (family_with (i:=i) u t) j=t*\prod_(j<k | j!=i) u j.
Proof.
rewrite (bigD1 i) // family_with_in; congr (_*_).
apply: eq_bigr=> j hj; rewrite family_with_out //.
by rewrite eq_sym.
Qed.

(** Source for [scalar_product_form_bounded]:
    a coefficient y defines the k-linear map
    (v_1,...,v_k) to (product v_i)y, including
    k= 0, in Federer 3.1.11, p. 220. *)
Lemma scalar_product_form_bounded (R : realType) k (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY) (y : Y) :
  norm_bounded_multilinear (fun t : R^o=>`|t|) NY
    (fun u : {ffun 'I_k->R^o}=>(\prod_(i<k) u i)*:y).
Proof.
split.
- move=> u i a t s; rewrite !scalar_family_product_replace.
  change (((a*t+s)*\prod_(j<k | j!=i) u j)*:y=
    a*:((t*\prod_(j<k | j!=i) u j)*:y)+
      ((s*\prod_(j<k | j!=i) u j)*:y)).
  by rewrite mulrDl -mulrA scalerDl scalerA.
- exists (NY y); split; first exact (real_seminorm_nonnegative hNY.1 y).
  move=> u; by rewrite (real_seminorm_scale hNY.1) normr_prod mulrC.
Qed.

Section ScalarForms.
Variable R : realType.
Variable k : nat.
Variables Y Z : lmodType R.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.
Variable evaluation : {ffun 'I_k->R^o}->Hom Z Y.
Variable ZN : Z->R.
Hypothesis hZ : is_continuous_multilinear_space (fun t : R^o=>`|t|) NY evaluation ZN.
Local Notation ones := ([ffun i : 'I_k=>(1:R^o)]).

(** Source for [continuous_multilinear_scalar_evaluation]:
    the one-dimensional multilinear evaluation formula,
    Federer 3.1.11, p. 220, first special case. *)
Theorem continuous_multilinear_scalar_evaluation u z :
  evaluation u z=(\prod_(i<k) u i)*:evaluation ones z.
Proof.
have hh := @multilinear_family_scale_all R k (fun _=>[the lmodType R of R^o])
  Y (fun v=>evaluation v z) (continuous_multilinear_evaluation hZ z) ones u.
have he : [ffun i : 'I_k=>u i*:ones i]=u.
  by apply/ffunP=> i; rewrite !ffunE; change (u i*1=u i); rewrite mulr1.
by rewrite he in hh.
Qed.

(** Source for [continuous_multilinear_scalar_norm]:
    the norm of a k-linear map with scalar source
    is the norm of its coefficient, supporting the
    real-source assertion in Federer 3.1.11, p. 220. *)
Theorem continuous_multilinear_scalar_norm z : ZN z=NY (evaluation ones z).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (multilinear_operator_least (continuous_multilinear_norm_laws hZ z)).
  + exact (real_seminorm_nonnegative hNY.1 (evaluation ones z)).
  + move=> u; rewrite continuous_multilinear_scalar_evaluation
      (real_seminorm_scale hNY.1) normr_prod mulrC; exact: lexx.
- have hh := multilinear_operator_bound (continuous_multilinear_norm_laws hZ z) ones.
  have hprod : \prod_(i<k) `|ones i|= 1.
    by apply: big1=> i _; rewrite ffunE normr1.
  by rewrite hprod mulr1 in hh.
Qed.

(** Source for [continuous_multilinear_scalar_injective]:
    the scalar-source coefficient determines the entire
    form, supporting Federer 3.1.11, p. 220. *)
Lemma continuous_multilinear_scalar_injective : injective (evaluation ones).
Proof.
move=> z w he; apply: (continuous_multilinear_extensional hZ)=> u.
by rewrite (continuous_multilinear_scalar_evaluation u z)
  (continuous_multilinear_scalar_evaluation u w) he.
Qed.

(** Source for [continuous_multilinear_scalar_surjective]:
    every target vector is a coefficient of a
    continuous scalar-source k-form, supporting Federer
    3.1.11, p. 220. *)
Lemma continuous_multilinear_scalar_surjective y :
  exists z, evaluation ones z=y.
Proof.
have [z hz] := continuous_multilinear_surjective hZ
  (@scalar_product_form_bounded R k Y NY hNY y).
exists z; rewrite hz.
have hprod : \prod_(i<k) ones i= 1 by apply: big1=> i _; rewrite ffunE.
by rewrite hprod scale1r.
Qed.

(** Source for [continuous_multilinear_scalar_identification]:
    existence of the isometric coefficient identification
    for real-source higher differentials, Federer 3.1.11,
    p. 220. It is derived from the abstract space
    laws, without exposing a carrier construction. *)
Theorem continuous_multilinear_scalar_identification :
  exists J : Hom Y Z,
    (forall y, evaluation ones (J y)=y) /\
    (forall z, J (evaluation ones z)=z) /\
    forall y, ZN (J y)=NY y.
Proof.
have [g hg] := choice continuous_multilinear_scalar_surjective.
have hlin : linear g.
  move=> c y w; apply: continuous_multilinear_scalar_injective.
  by rewrite hg linearD linearZ /= !hg.
pose J := @HomMap R Y Z g (introT (asboolP _) hlin).
exists J; split; first exact hg.
split.
- move=> z; apply: continuous_multilinear_scalar_injective; exact: hg.
- move=> y; by rewrite continuous_multilinear_scalar_norm hg.
Qed.
End ScalarForms.
