(** Federer (1969), 3.4.8(11), p. 335:
    the norm of the next prefix is at
    most the preceding prefix norm plus the
    absolute value of the last coordinate.
    Apply the existing transverse split of 3.4.6. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP WeierstrassTransverseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_split_norm_bound]:
    the prefix norm estimate in the
    nested-root argument, 3.4.8(11), p. 335. *)
Theorem weierstrass_split_norm_bound (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) v (xi:Hom X R^o)
    (inclusion:Hom K X) (projection:Hom X K):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->NX v = 1 ->
  forall x,NX x<=NK (projection x)+`|xi x|.
Proof.
move=>hSplit hUnit x.
have hRestore:inclusion (projection x)+(xi x)*:v = x.
  by rewrite (weierstrass_transverse_projection_equation hSplit) subrK.
have hBound:=real_seminorm_triangle hNX.1 (inclusion (projection x)) ((xi x)*:v).
rewrite hRestore (weierstrass_transverse_inclusion_norm hSplit)
  (real_seminorm_scale hNX.1) hUnit mulr1 in hBound.
exact:hBound.
Qed.
