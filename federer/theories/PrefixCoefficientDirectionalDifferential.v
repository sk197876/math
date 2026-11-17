(** Federer (1969), 3.4.8(10), p. 331:
    the original prefix coefficient differentials
    vanish on the next coordinate direction.
    Apply the existing linear differential,
    chain rule and domain restriction laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialChain NormDifferentialLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [prefix_coefficient_directional_differential]:
    each actual original coefficient b composed
    with p_m has directional derivative zero
    along e_(m+1), supporting the displayed
    differential calculation in 3.4.8(10), p. 331.
    The exact prefix equation P(v)=0 is
    retained, and no derivative conclusion is assumed. *)
Theorem prefix_coefficient_directional_differential (R:realType) (X Y:lmodType R)
  (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
  (A:X->Prop) (U:Y->Prop) (P:Hom X Y) (b:Y->R) (a v:X) (D:Hom Y R^o):
  norm_domain_interior NX A a ->norm_bounded_linear NX NY P ->
  (forall x,A x ->U (P x)) ->P v = 0 ->
  has_norm_differential NY (fun t:R^o=>`|t|) U b (P a) D ->
  has_norm_differential NX (fun t:R^o=>`|t|) A (fun x=>b (P x)) a (hom_comp D P) /\
    (hom_comp D P) v = 0.
Proof.
move=>hInterior hP hMaps hZero hB.
have hLinear:=@norm_differential_linear R X Y NX NY hNX hNY A a P hInterior hP.
have hChain:=@norm_differential_chain R X Y R^o NX NY (fun t:R^o=>`|t|)
  hNX hNY (@scalar_absolute_value_norm R) A U P b a P D hLinear hB.
split.
- exact:(@norm_differential_restrict R X R^o NX (fun t:R^o=>`|t|)
    (fun x=>A x /\U (P x)) A (fun x=>b (P x)) a (hom_comp D P)
    (fun x hx=>conj hx (hMaps x hx)) hInterior hChain).
- by rewrite hom_compE hZero linear0.
Qed.
