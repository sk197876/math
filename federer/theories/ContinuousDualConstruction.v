(** Private carrier construction for the continuous dual in Federer (1969),
    2.4.12, p. 87. Continuous maps form a subspace of the project's
    algebraic Hom space. Its proved norm uses only the sealed least-bound
    interface. Source context: ContinuousDualUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier RealNormUP
  ContinuousRealFunctional ContinuousFunctionalSpace RealFunctionalNormUP
  RealFunctionalNormSealed ContinuousDualUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Construction.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.

(** Source for [continuous_functional_subspace]: supporting
    subspace witness for Y*, Federer 2.4.12, p. 87. *)
Definition continuous_functional_subspace : subspace (Hom V R^o) :=
  @Subspace R (Hom V R^o)
    (fun a => is_continuous_real_functional hN (hom_as_linear a))
    (@continuous_hom_zero R V N hN) (@continuous_hom_add R V N hN)
    (fun c a => @continuous_hom_scale R V N hN a c).

(** Source for [continuous_dual_carrier]: private carrier
    witnessing the abstract dual, Federer 2.4.12, p. 87. *)
Definition continuous_dual_carrier : lmodType R :=
  [the lmodType R of subspace_space continuous_functional_subspace].

(** Source for [continuous_dual_evaluation]: linear evaluation
    map of the constructed dual, Federer 2.4.12, p. 87. *)
Definition continuous_dual_evaluation : Hom continuous_dual_carrier (Hom V R^o) :=
  hom_of_linear (subspace_inclusion continuous_functional_subspace).

(** Source for [continuous_dual_carrier_norm]: the sealed least
    bound supplies the dual norm, Federer 2.4.12, p. 87. *)
Definition continuous_dual_carrier_norm (a : continuous_dual_carrier) : R :=
  RealFunctionalNorm.value (subspace_valP a).

(** Source for [continuous_dual_carrier_laws]: existence witness
    satisfying the abstract dual specification, Federer 2.4.12, p. 87. *)
Theorem continuous_dual_carrier_laws :
  is_continuous_dual hN continuous_dual_evaluation continuous_dual_carrier_norm.
Proof.
split.
- exact: subspace_val_injective.
- exact: subspace_valP.
- move=> a ha; exists (@subspace_lift R (Hom V R^o) continuous_functional_subspace a ha); by [].
- move=> a; exact: RealFunctionalNorm.laws.
Qed.
End Construction.
