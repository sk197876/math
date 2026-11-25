(** Federer (1969), 3.2.28(1), printed p. 263: polynomial
    calculus on Hom spaces is independent of the equivalent finite
    dimensional norms, whereas their geometric volumes use 1.7.9.
    This adapter proves the norm changes from finite linear bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP LinearBasis NormDifferentialUP
  NormFiniteLinearBound NormRegularity NormRegularityLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_class_finite_norm_change]: the norm
    equivalence implicit for finite-dimensional polynomial maps
    in Federer 3.2.28(1), p. 263; equivalence of norms is
    recalled in 2.7.16, p. 134. The class and actual domain
    are unchanged. Both identity maps are proved bounded. *)
Theorem norm_class_finite_norm_change (R:realType) (X Y:lmodType R)
    (NX MX:X->R) (NY MY:Y->R)
    (hNX:is_real_norm NX) (hMX:is_real_norm MX)
    (hNY:is_real_norm NY) (hMY:is_real_norm MY)
    n (b:'I_n->X) (hb:is_basis b) p (c:'I_p->Y) (hc:is_basis c)
    (A:X->Prop) (f:X->Y) k:
  norm_class hNX hNY A f k ->norm_class hMX hMY A f k.
Proof.
move=>hf.
have hIn:norm_bounded_linear MX NX (hom_of_linear (linear_id X)).
  exact:(norm_finite_linear_bounded hMX hNX hb _).
have hOut:norm_bounded_linear NY MY (hom_of_linear (linear_id Y)).
  exact:(norm_finite_linear_bounded hNY hMY hc _).
have hg:=@norm_class_precompose_linear R X X Y MX NX NY hMX hNX hNY
  A f (hom_of_linear (linear_id X)) k hIn hf.
exact:(@norm_class_postcompose_linear R X Y Y MX NY MY hMX hNY hMY
  A f (hom_of_linear (linear_id Y)) k hOut hg).
Qed.
