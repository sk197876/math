(** Federer (1969), 1.6.6, pp. 26-27: a complex vector space is also a real
    vector space. This supporting interface makes the change of scalar field
    explicit; the underlying additive group is unchanged. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [restricted_space]: Federer 1.6.6, p. 26, opening
    paragraph. Construction of the underlying space over the smaller
    field, supporting the real and complex alternating-form comparison. *)
Definition restricted_space (R C : fieldType) (embed : {rmorphism R -> C})
    (V : Type) := V.

HB.instance Definition _ (R C : fieldType) (embed : {rmorphism R -> C})
    (V : choiceType) := Choice.copy (restricted_space embed V) V.
HB.instance Definition _ (R C : fieldType) (embed : {rmorphism R -> C})
    (V : zmodType) := GRing.Zmodule.copy (restricted_space embed V) V.

Section Restriction.
Variables R C : fieldType.
Variable embed : {rmorphism R -> C}.
Variable V : lmodType C.
Local Notation VR := (restricted_space embed V).

(** Source for [restricted_scale]: Federer 1.6.6, p. 26, opening
    paragraph. The scalar action obtained by embedding the smaller field. *)
Definition restricted_scale (a : R) (x : VR) : VR := embed a *: x.

(** Source for [restricted_scaleA]: Federer 1.6.6, p. 26, opening
    paragraph. Supporting verification of the restricted module laws. *)
Lemma restricted_scaleA a b x :
  restricted_scale a (restricted_scale b x) = restricted_scale (a * b) x.
Proof. by rewrite /restricted_scale rmorphM scalerA. Qed.

(** Source for [restricted_scale1]: Federer 1.6.6, p. 26, opening
    paragraph. Supporting verification of the restricted module laws. *)
Lemma restricted_scale1 : left_id 1 restricted_scale.
Proof. by move=> x; rewrite /restricted_scale rmorph1 scale1r. Qed.

(** Source for [restricted_scaleDr]: Federer 1.6.6, p. 26, opening
    paragraph. Supporting verification of the restricted module laws. *)
Lemma restricted_scaleDr a : {morph restricted_scale a : x y / x + y}.
Proof. by move=> x y; rewrite /restricted_scale scalerDr. Qed.

(** Source for [restricted_scaleDl]: Federer 1.6.6, p. 26, opening
    paragraph. Supporting verification of the restricted module laws. *)
Lemma restricted_scaleDl x : {morph restricted_scale^~ x : a b / a + b}.
Proof. by move=> a b; rewrite /restricted_scale rmorphD scalerDl. Qed.
HB.instance Definition _ := GRing.Zmodule_isLmodule.Build R VR
  restricted_scaleA restricted_scale1 restricted_scaleDr restricted_scaleDl.
End Restriction.

Section Maps.
Variables R C : fieldType.
Variable embed : {rmorphism R -> C}.
Variables V W : lmodType C.
Variable f : {linear V -> W}.

(** Source for [restricted_function]: Federer 1.6.6, pp. 26-27,
    complex linear forms and endomorphisms considered over R.
    The underlying function with restricted domain and codomain. *)
Definition restricted_function (x : restricted_space embed V) :
  restricted_space embed W := f x.

(** Source for [restricted_function_linear]: Federer 1.6.6, pp. 26-27,
    complex linear forms and endomorphisms considered over R.
    Supporting verification that complex linearity implies real linearity. *)
Lemma restricted_function_linear : linear restricted_function.
Proof. by move=> a x y; exact: (linearP f (embed a) x y). Qed.
HB.instance Definition _ := GRing.isLinear.Build R
  (restricted_space embed V) (restricted_space embed W) *:%R
  restricted_function restricted_function_linear.

(** Source for [restrict_linear]: Federer 1.6.6, pp. 26-27, complex
    linear forms and endomorphisms considered over R. Construction of
    the same map with its restricted linearity. *)
Definition restrict_linear :
    {linear restricted_space embed V -> restricted_space embed W} :=
  GRing.Linear.clone _ _ _ _ restricted_function _.
End Maps.
