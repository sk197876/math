(** Federer (1969), 3.1.21, p. 234: differentiable maps send
    tangent vectors to tangent vectors of the image. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocal
  TangentConeUP TangentConeBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_differential_tangent_image]: Df(a)[Tan(S,a)]
    is contained in Tan[f(S),f(a)], Federer 3.1.21, p. 234,
    first displayed inclusion. The local domain is explicit;
    only S intersect that domain is needed for the image witness.
    No completeness, finite dimension or injectivity is used. *)
Theorem norm_differential_tangent_image (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:set X) (f:X->Y) a (L:Hom X Y) :
  has_norm_differential NX NY A f a L ->
  forall v,norm_tangent_cone NX S a v ->
    norm_tangent_cone NY (f @` (S `&` A)) (f a) (L v).
Proof.
move=>hf v hv e he.
have [C [hC hL]]:=norm_differential_bounded hf.
have [ra [hra hA]]:=norm_differential_interior hf.
have hn:=real_seminorm_nonnegative hNX.1 v.
pose t:=e/(4*(NX v+1)).
have ht:0<t by rewrite /t divr_gt0 // mulr_gt0 //; lra.
have htE:t*(4*(NX v+1))=e by rewrite /t divfK //; apply/eqP; lra.
have [rd [hrd hrem]]:=norm_differential_remainder hf ht.
have [rc [hrc hcont]]:=norm_differential_continuous_at hNY hf he.
pose d:=Num.min ra (Num.min rd rc).
have hd:0<d by rewrite /d !lt_min hra hrd hrc.
pose q:=Num.min 1 (e/(4*(C+1))).
have hq:0<q by rewrite /q lt_min ltr01 divr_gt0 // mulr_gt0 //; lra.
have [x [r [hx [hr [hxd hxq]]]]]:=(@norm_tangent_two_radii R X NX S a v).1 hv d q hd hq.
pose h:=x-a.
have hxa:a+h=x by rewrite /h addrC subrK.
have hhra:NX h<ra:=lt_le_trans hxd (real_minimum_left_bound ra (Num.min rd rc)).
have hhrd:NX h<rd.
  exact (lt_le_trans hxd (le_trans (real_minimum_right_bound ra (Num.min rd rc)) (real_minimum_left_bound rd rc))).
have hhrc:NX h<rc.
  exact (lt_le_trans hxd (le_trans (real_minimum_right_bound ra (Num.min rd rc)) (real_minimum_right_bound rd rc))).
have hAx:A x by rewrite -hxa; exact: hA h hhra.
have hfv:NY (f x-f a)<e by rewrite -hxa; exact: hcont h (hA h hhra) hhrc.
have hre:=hrem h (hA h hhra) hhrd; rewrite hxa in hre.
have hq1:q<=1:=real_minimum_left_bound 1 (e/(4*(C+1))).
have hqe:q*(4*(C+1))<=e.
  have hh:=real_minimum_right_bound 1 (e/(4*(C+1))).
  rewrite ler_pdivlMr in hh; first exact hh.
  apply: mulr_gt0; lra.
have hq0:=ltW hq.
have htri:NX (r*:h)<=NX (r*:h-v)+NX v.
  have hh:=real_seminorm_triangle hNX.1 (r*:h-v) v.
  by rewrite subrK in hh.
have hrnorm:NX (r*:h)=r*NX h by rewrite (real_seminorm_scale hNX.1) (ger0_norm (ltW hr)).
have hscaled:NY (r*:(f x-f a-L h))<=r*(t*NX h).
  rewrite (real_seminorm_scale hNY.1) (ger0_norm (ltW hr)).
  exact (ler_wpM2l (ltW hr) hre).
have hlinear:NY (L (r*:h-v))<=C*NX (r*:h-v):=hL _.
have heq:r*:(f x-f a)-L v=r*:(f x-f a-L h)+L (r*:h-v).
  have hlin:L (r*:h-v)=r*:L h-L v by rewrite linearB linearZ.
  by rewrite hlin [r*:(f x-f a-L h)]scalerBr addrA subrK.
have hb:=real_seminorm_triangle hNY.1 (r*:(f x-f a-L h)) (L (r*:h-v)).
rewrite -heq in hb.
have hxq0:=real_seminorm_nonnegative hNX.1 (r*:h-v).
have hnh:=real_seminorm_nonnegative hNX.1 h.
exists (f x),r; split; first by exists x.
split=>//; split=>//.
change (NY (r*:(f x-f a)-L v)<e).
change (is_true (NX (r*:h-v)<q)) in hxq.
nra.
Qed.
