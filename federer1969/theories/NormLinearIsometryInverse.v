(** Federer (1969), 3.1.11, p. 219:
    an onto linear isometry has a linear isometric
    inverse. This supports transporting derivative
    representatives between the two groupings of arguments. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_linear_isometry_inverse_exists]:
    the inverse identification for grouped multilinear
    maps in Federer 3.1.11, p. 219.
    Only existence and both inverse/norm laws
    are exposed, with arbitrary normed source
    and target spaces. *)
Theorem norm_linear_isometry_inverse_exists (R : realType)
    (V W : lmodType R) (NV : V->R) (NW : W->R)
    (hNV : is_real_norm NV) (hNW : is_real_norm NW)
    (J : Hom V W) :
  (forall v, NW (J v)=NV v) ->
  (forall w, exists v, J v=w) ->
  exists K : Hom W V,
    (forall v, K (J v)=v) /\
    (forall w, J (K w)=w) /\
    (forall w, NV (K w)=NW w).
Proof.
move=> hN hsurj.
have hinj : injective J.
  move=> v u h; apply/eqP; rewrite -subr_eq0; apply/eqP; apply: hNV.2.
  by rewrite -hN linearB /= h subrr (real_seminorm_zero hNW.1).
have [k hk] := choice hsurj.
have hlin : linear k.
  move=> c x y; apply: hinj.
  by rewrite linearP /= !hk.
pose K := @HomMap R W V k (introT (asboolP _) hlin).
exists K; split.
- move=> v; apply: hinj; exact: hk.
- split; first exact hk.
  move=> w; by rewrite -hN /K /= hk.
Qed.


(** Source for [norm_linear_isometry_bounded]:
    an isometric linear identification is bounded
    with constant one, supporting transport of
    higher differentials in Federer 3.1.11, p. 219. *)
Lemma norm_linear_isometry_bounded (R : realType) (V W : lmodType R)
    (NV : V->R) (NW : W->R) (J : Hom V W) :
  (forall v, NW (J v)=NV v) -> norm_bounded_linear NV NW J.
Proof.
move=> h; exists 1; split; first exact: ler01.
by move=> v; rewrite h mul1r.
Qed.
