(** Federer (1969), 1.7.5, pp. 31-32: public maps gamma and gamma_m, and the
    associated bilinear form on m-vectors. This interface uses only the
    sealed extension laws. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity InnerExteriorUP InnerExteriorSealed
  AlgebraUP ExteriorAlgebra ExteriorGrading GradedAlgebra GradedComponents
  AlternatingCoordinates AlternatingPairing AlternatingUnit ScalarCoefficients
  BilinearPrecompose TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Interface.
Variable R : realFieldType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [inner_exterior_extension]: Federer 1.7.5,
    p. 31, the unique algebra extension gamma, given by its
    sealed abstract specification. *)
Definition inner_exterior_extension := @InnerExterior.map R h2 V B hB.

(** Source for [inner_exterior_extensionP]: Federer 1.7.5,
    p. 31, gamma satisfies the defining extension laws. *)
Lemma inner_exterior_extensionP : is_inner_exterior_extension hB inner_exterior_extension.
Proof. exact: InnerExterior.laws. Qed.

(** Source for [inner_exterior_generator]: Federer 1.7.5,
    p. 31, gamma extends beta on the generating vectors. *)
Lemma inner_exterior_generator v :
  inner_exterior_extension (exterior_generator v) = form_include (inner_polarity hB v).
Proof. exact (@inner_exterior_extension_generator R h2 V B hB
  inner_exterior_extension inner_exterior_extensionP v). Qed.

(** Source for [inner_exterior_form]: Federer 1.7.5,
    p. 31, gamma_m is the restriction of gamma to degree m. *)
Definition inner_exterior_form m (x : exterior_power V m) : A_m V R^o m :=
  form_component m (inner_exterior_extension (component_val x)).

(** Source for [inner_exterior_form_linear]: Federer
    1.7.5, p. 31, the degree restrictions gamma_m are linear. *)
Lemma inner_exterior_form_linear m : linear (@inner_exterior_form m).
Proof. move=> a x y; by rewrite /inner_exterior_form !linearP. Qed.
HB.instance Definition _ m := GRing.isLinear.Build R (exterior_power V m)
  (A_m V R^o m) *:%R (@inner_exterior_form m) (@inner_exterior_form_linear m).

(** Source for [inner_exterior_form_include]: Federer
    1.7.5, p. 31, gamma is the direct sum of its degree restrictions. *)
Lemma inner_exterior_form_include m (x : exterior_power V m) :
  form_include (inner_exterior_form x) = inner_exterior_extension (component_val x).
Proof.
rewrite /inner_exterior_form form_componentK.
exact (@inner_exterior_extension_graded R h2 V B hB
  inner_exterior_extension inner_exterior_extensionP m _ (component_homogeneous x)).
Qed.

(** Source for [exterior_inner_form]: Federer 1.7.5,
    p. 32, first display: xi dot eta is evaluation of gamma_m(eta)
    against xi, equivalently evaluation of beta_m(eta). *)
Definition exterior_inner_form m (x y : exterior_power V m) : R :=
  pairing x (inner_exterior_form y).

(** Source for [exterior_inner_form_bilinear]: Federer
    1.7.5, pp. 31-32, the induced function is bilinear. *)
Lemma exterior_inner_form_bilinear m :
  @bilinear R (exterior_power V m) (exterior_power V m) R^o (@exterior_inner_form m).
Proof.
exact: (bilinear_linear_precompose (@pairing_bilinear R V R^o m)
  (linear_id (exterior_power V m))
  (GRing.Linear.clone _ _ _ _ (@inner_exterior_form m) _)).
Qed.
End Interface.
