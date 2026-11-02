(** Federer (1969), 3.1.21, p. 234: tangent and normal
    bundles represented in the standard linear identification
    R^n times R^n = R^(n+n). *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  EuclideanBlockLinearMaps TangentConeUP NormalConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_tangent_bundle]: Tan(B) in Federer
    3.1.21, pp. 233–234, through the existing block
    identification of the Cartesian ambient product. *)
Definition euclidean_tangent_bundle (R:realType) n (B:set (R_n R n)) : set (R_n R (n+n)) :=
  fun z=>B (@euclidean_first_block_map R n n z) /\
    norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) B
      (@euclidean_first_block_map R n n z) (@euclidean_last_block_map R n n z).

(** Source for [euclidean_normal_bundle]: Nor(B) in Federer
    3.1.21, p. 234, through the same Cartesian block
    identification; the normal-cone sign convention is retained. *)
Definition euclidean_normal_bundle (R:realType) n (B:set (R_n R n)) : set (R_n R (n+n)) :=
  fun z=>B (@euclidean_first_block_map R n n z) /\
    inner_normal_cone (inner_norm (@euclidean_inner_productP R n)) (@euclidean_inner_product R n) B
      (@euclidean_first_block_map R n n z) (@euclidean_last_block_map R n n z).

(** Source for [euclidean_derivative_lift]: the induced tangent
    coordinate change (x,v) -> (f(x),Df(x)v) underlying
    the bundle assertion in Federer 3.1.21, p. 234.
    The supplied derivative field must satisfy actual graph laws
    in every theorem using this formula. *)
Definition euclidean_derivative_lift (R:realType) n
    (f:R_n R n->R_n R n) (D:R_n R n->Hom (R_n R n) (R_n R n))
    (z:R_n R (n+n)) : R_n R (n+n) :=
  @euclidean_first_injection_map R n n (f (@euclidean_first_block_map R n n z))+
  @euclidean_last_injection_map R n n
    (D (@euclidean_first_block_map R n n z) (@euclidean_last_block_map R n n z)).
