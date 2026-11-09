(** Federer (1969), 3.4.6, p. 322: the
    original nonzero distinguished direction admits a bounded
    scalar functional taking value one on it. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear SeminormNormingFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_direction_functional_exists]:
    the bounded functional used for the original transverse
    splitting exists for every nonzero v, 3.4.6,
    p. 322. The project's proved Hahn–Banach corollary
    supplies it; no functional or coordinates are assumed
    in the final division theorem. *)
Theorem weierstrass_direction_functional_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (v:X):v<>0 ->
  exists xi:Hom X R^o,norm_bounded_linear NX (fun r:R^o=>`|r|) xi /\xi v= 1.
Proof.
move=>hV.
have hNonzero:v!=0 by apply/eqP.
have hPositive:0<NX v by rewrite (real_norm_positive hNX.1 hNX.2).
have hNormNonzero:NX v!=0 by rewrite (gt_eqF hPositive).
have [f [hBound hValue]]:=@seminorm_norming_functional R X NX hNX.1 v.
have hF:norm_bounded_linear NX (fun r:R^o=>`|r|) (hom_of_linear f).
  exists 1;split;first exact:ler01.
  move=>x;rewrite mul1r;exact:hBound x.
exists ((NX v)^-1*:hom_of_linear f);split.
- exact:(norm_bounded_linear_scale (@scalar_absolute_value_norm R) _ hF).
- rewrite hom_scaleE.
  change ((NX v)^-1*f v= 1).
  by rewrite hValue mulVf.
Qed.
