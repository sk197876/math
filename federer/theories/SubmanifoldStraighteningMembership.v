(** Federer (1969), 3.1.21, p. 234: exact set
    membership in the straightening charts of 3.1.19. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom ModuleQuotient GrassmannSubspaces GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormDiffeomorphismUP EuclideanSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [submanifold_straightening_membership]: supporting
    the tangent and normal bundle charts of Federer 3.1.21,
    p. 234. On the actual source chart domain T,
    x belongs to B exactly when sigma(x) lies in its plane. *)
Lemma submanifold_straightening_membership (R:realType) n mu k
    (B T C:set (R_n R n)) b s t (Z:G (R_n R n) mu) :
  @is_submanifold_straightening R n mu k B b T C s t Z ->
  forall x,T x -> (B x <-> grassmann_val Z (s x)).
Proof.
move=>hChart x hx.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hD:=submanifold_straightening_diffeomorphism hChart.
have him:=submanifold_straightening_image hChart.
split.
- move=>hb; have hi:(s @` (B `&` T)) (s x) by exists x; split.
  rewrite him in hi; exact hi.1.
- move=>hz.
  have hsx:=@norm_diffeomorphism_maps R X X NX NX hNX hNX T C s t k hD x hx.
  have hi:(s @` (B `&` T)) (s x) by rewrite him; split.
  have [y [hyB hyT] hyx]:=hi.
  have he:=congr1 t hyx.
  rewrite (@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX T C s t k hD y hyT)
    (@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX T C s t k hD x hx) in he.
  by rewrite -he.
Qed.
