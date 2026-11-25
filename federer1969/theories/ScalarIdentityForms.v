(** Federer (1969), 3.1.24, p. 240: the scalar
    identity has normalized first coefficient one and all
    other coefficients zero at zero, on its actual open domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom NormDifferentialUP ContinuousMultilinearUP NormHigherDifferentialUP
  NormHigherSymmetricFormUP ScalarAffineDifferentials ScalarCoefficientForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_identity_form_actual]: actual higher
    forms of the scalar identity on an arbitrary open domain
    containing zero, supporting the composition inverse identity
    in Federer 3.1.24, p. 240. Its coefficients are
    those of the affine map x mapped to x. *)
Theorem scalar_identity_form_actual (R:realType)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->R^o}->Hom (Z i) R^o)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) (@ev i) (@ZN i))
    (A:R^o->Prop) (hA:forall x,A x -> norm_domain_interior (fun t:R^o=>`|t|) A x) m :
  A 0 -> is_norm_higher_differential_form (fun t:R^o=>`|t|) ev ZN A (fun x=>1*x+0) m 0
    (scalar_coefficient_form m (scalar_affine_derivative_coefficient 1 0 m 0)).
Proof.
move=>h0.
have [_ [D [hD [hE _]]]]:=@scalar_affine_higher_differentials R Z ev ZN hZ A hA 1 0.
exact (@scalar_coefficient_form_actual R Z ev ZN A (fun x=>1*x+0) m 0 (D m 0)
  (scalar_affine_derivative_coefficient 1 0 m 0) (hD m 0 h0) (hE m 0)).
Qed.
