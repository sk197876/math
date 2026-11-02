(** Federer (1969), 3.2.28(4), printed p. 266:
    tangents to a subset of the unit sphere are perpendicular
    to the base point. The actual norm differential and
    tangent-image theorem prove this supporting fact in an
    arbitrary real inner-product space. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  InnerNormDifferential TangentConeUP TangentConeBasic TangentDifferentialImage TangentSingleton.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [unit_sphere_subset_tangent_orthogonal]:
    h perpendicular to x for h tangent to a submanifold
    of the unit sphere, used in Federer 3.2.28(4),
    p. 266. The stronger supporting statement needs
    no submanifold regularity or finite-dimensional assumption. *)
Theorem unit_sphere_subset_tangent_orthogonal (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (S:set V) (x:V):
  (forall y,S y ->inner_norm hB y= 1) ->inner_norm hB x= 1 ->
  forall v,norm_tangent_cone (inner_norm hB) S x v ->B x v=0.
Proof.
move=>hS hx v hv.
have hNz:x!=0.
  apply/eqP=>hz; move:hx; rewrite hz inner_norm0=>/eqP.
  by rewrite eq_sym oner_eq0.
have hd:=inner_norm_differential hB hNz.
have ht:=@norm_differential_tangent_image R V R^o (inner_norm hB)
  (fun r:R^o=>`|r|) (inner_norm_real_norm hB) (scalar_absolute_value_norm R)
  setT S (fun y=>(inner_norm hB y:R^o)) x (inner_norm_gradient hB x) hd v hv.
have hSub:((fun y:V=>(inner_norm hB y:R^o)) @` (S `&` setT)) `<=` [set (1:R^o)].
  move=>y [z [hz _] <-]; exact:hS z hz.
have hh:=@norm_tangent_mono R R^o (fun r:R^o=>`|r|) _ _
  (inner_norm hB x) hSub (inner_norm_gradient hB x v) ht.
rewrite hx (@norm_tangent_singleton R R^o _ (scalar_absolute_value_norm R) 1) in hh.
change ((inner_norm hB x)^-1*B x v=0) in hh.
by rewrite hx invr1 mul1r in hh.
Qed.
