(** Federer (1969), 3.1.18, p. 229: shrink the image of the local
    source diffeomorphism to a product of convex neighbourhoods. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  NormClassOneUP NormClassZeroComposition NormRegularity NormRegularityOperations
  NormDiffeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_diffeomorphism_target_restriction]: restricting
    the image to an open subset and the source to its inverse image
    preserves the diffeomorphism, supporting the convex V,W shrinking
    in Federer 3.1.18, p. 229. *)
Theorem norm_diffeomorphism_target_restriction (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (B W:Y->Prop) (f:X->Y) (g:Y->X) k :
  is_norm_diffeomorphism hNX hNY A B f g k ->
  (forall y, W y -> B y) ->
  (forall y, W y -> norm_domain_interior NY W y) ->
  is_norm_diffeomorphism hNX hNY (fun x=>A x /\ W (f x)) W f g k.
Proof.
move=>hD hWB hWopen.
have hf:=@norm_diffeomorphism_forward_class R X Y NX NY hNX hNY A B f g k hD.
have hg:=@norm_diffeomorphism_inverse_class R X Y NX NY hNX hNY A B f g k hD.
pose IY:=hom_of_linear (linear_id Y).
have hI:norm_bounded_linear NY NY IY.
  exists 1; split; first exact: ler01.
  by move=>y; change (NY y<=1*NY y); rewrite mul1r.
have hId:=@norm_class_linear R Y Y NY NY hNY hNY W IY 0%N hWopen hI.
have hf0:=@norm_class_continuous R X Y NX NY hNX hNY A f k hf.
have hI0:=@norm_class_continuous R Y Y NY NY hNY hNY W IY 0%N hId.
have hUopen:=@norm_class_zero_composite_interior R X Y Y NX NY NY A W f IY hf0 hI0.
constructor.
- exact: norm_diffeomorphism_spaces hD.
- exact (@norm_class_open_restriction R X Y NX NY hNX hNY A
    (fun x=>A x /\ W (f x)) f k (fun x hx=>hx.1) hUopen hf).
- exact (@norm_class_open_restriction R Y X NY NX hNY hNX B W g k hWB hWopen hg).
- by move=>x hx; exact hx.2.
- move=>y hy; split.
  + exact (@norm_diffeomorphism_inverse_maps R X Y NX NY hNX hNY A B f g k hD y (hWB y hy)).
  + by rewrite (@norm_diffeomorphism_right_inverse R X Y NX NY hNX hNY A B f g k hD y (hWB y hy)).
- move=>x hx; exact (@norm_diffeomorphism_left_inverse R X Y NX NY hNX hNY A B f g k hD x hx.1).
- move=>y hy; exact (@norm_diffeomorphism_right_inverse R X Y NX NY hNX hNY A B f g k hD y (hWB y hy)).
Qed.
