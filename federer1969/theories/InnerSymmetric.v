(** Federer (1969), 1.10.5, p. 47, the polarity extension and induced
    bilinear form on symmetric powers. This public interface uses only the
    sealed extension laws. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerSymmetricPolarity InnerSymmetricUP InnerSymmetricSealed
  AlgebraUP SymmetricAlgebra SymmetricGrading GradedAlgebra GradedComponents
  SymmetricForms SymmetricFormSum SymmetricPairing SymmetricFormUnit ScalarCoefficients
  BilinearPrecompose TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Interface.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [inner_symmetric_extension]: Federer 1.10.5, p. 47,
    first paragraph. In words: The unique algebra extension gamma is exposed only through its sealed laws. *)
Definition inner_symmetric_extension := @InnerSymmetric.map R V B hB.

(** Source for [inner_symmetric_extensionP]: Federer 1.10.5, p. 47,
    first paragraph. In words: The public extension satisfies the generator and grading specification. *)
Lemma inner_symmetric_extensionP : is_inner_symmetric_extension hB inner_symmetric_extension.
Proof. exact: InnerSymmetric.laws. Qed.

(** Source for [inner_symmetric_generator]: Federer 1.10.5, p. 47,
    first paragraph. In words: The extension agrees with the given polarity on every generator. *)
Lemma inner_symmetric_generator v :
  inner_symmetric_extension (symmetric_generator v) = sform_include (inner_symmetric_polarity hB v).
Proof. exact (@inner_symmetric_extension_generator R V B hB
  inner_symmetric_extension inner_symmetric_extensionP v). Qed.

(** Source for [inner_symmetric_form]: Federer 1.10.5, p. 47,
    first paragraph. In words: The degree-m map is the restriction of gamma to the m-th symmetric power. *)
Definition inner_symmetric_form m (x : symmetric_power V m) : S_m V R^o m :=
  sform_component m (inner_symmetric_extension (component_val x)).

(** Source for [inner_symmetric_form_linear]: Federer 1.10.5, p. 47,
    first paragraph. In words: Each homogeneous restriction is linear. *)
Lemma inner_symmetric_form_linear m : linear (@inner_symmetric_form m).
Proof. move=> a x y; by rewrite /inner_symmetric_form !linearP. Qed.
HB.instance Definition _ m := GRing.isLinear.Build R (symmetric_power V m)
  (S_m V R^o m) *:%R (@inner_symmetric_form m) (@inner_symmetric_form_linear m).

(** Source for [inner_symmetric_form_include]: Federer 1.10.5, p. 47,
    first paragraph. In words: Including the restriction recovers gamma on a homogeneous vector. *)
Lemma inner_symmetric_form_include m (x : symmetric_power V m) :
  sform_include (inner_symmetric_form x) = inner_symmetric_extension (component_val x).
Proof.
rewrite /inner_symmetric_form sform_componentK.
exact (@inner_symmetric_extension_graded R V B hB
  inner_symmetric_extension inner_symmetric_extensionP m _ (component_homogeneous x)).
Qed.

(** Source for [symmetric_inner_form]: Federer 1.10.5, p. 47,
    first paragraph. In words: Pair a symmetric vector with the image of the other vector under gamma_m. Positivity is proved separately. *)
Definition symmetric_inner_form m (x y : symmetric_power V m) : R :=
  symmetric_pairing x (inner_symmetric_form y).

(** Source for [symmetric_inner_form_bilinear]: Federer 1.10.5, p. 47,
    first paragraph. In words: The resulting function is bilinear, by bilinearity of the pairing and linearity of gamma_m. *)
Lemma symmetric_inner_form_bilinear m :
  @bilinear R (symmetric_power V m) (symmetric_power V m) R^o (@symmetric_inner_form m).
Proof.
exact: (bilinear_linear_precompose (@symmetric_pairing_bilinear R V R^o m)
  (linear_id (symmetric_power V m))
  (GRing.Linear.clone _ _ _ _ (@inner_symmetric_form m) _)).
Qed.
End Interface.
