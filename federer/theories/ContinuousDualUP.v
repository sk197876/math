(** Federer (1969), 2.4.12, p. 87: Y* is the space of continuous real linear
    functionals with its dual norm. This abstract specification
    characterises the space by evaluation, without fixing its carrier
    implementation. continuity and the norm are additional structure here. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousRealFunctional RealFunctionalNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_continuous_dual]: abstract specification of
    the normed continuous dual in Federer 2.4.12, p. 87. *)
Record is_continuous_dual (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (D : lmodType R)
    (evaluation : Hom D (Hom V R^o)) (DN : D -> R) : Prop := {
  (** Source for [continuous_dual_injective]: a functional is
      determined by its evaluations, Federer 2.4.12, p. 87. *)
  continuous_dual_injective : injective evaluation;
  (** Source for [continuous_dual_continuous]: each element is a
      continuous functional, Federer 2.4.12, p. 87. *)
  continuous_dual_continuous : forall a : D,
    is_continuous_real_functional hN (hom_as_linear (evaluation a));
  (** Source for [continuous_dual_surjective]: the dual contains
      every continuous functional, Federer 2.4.12, p. 87. *)
  continuous_dual_surjective : forall a : Hom V R^o,
    is_continuous_real_functional hN (hom_as_linear a) ->
    exists d : D, evaluation d = a;
  (** Source for [continuous_dual_norm_laws]: the dual norm is
      the least evaluation bound, Federer 2.4.12, p. 87. *)
  continuous_dual_norm_laws : forall d : D,
    is_real_functional_norm N (hom_as_linear (evaluation d)) (DN d)
}.
