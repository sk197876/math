(** Federer (1969), 3.1.19, p. 231: condition (1) implies (4).
    An adapted linear chart and a product neighbourhood give convex
    coordinate parameters. This also works at class zero and mu=0. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerConvex HilbertFormCompactness NormDifferentialUP NormRegularity NormRegularityOperations
  NormFiniteLinearBound NormOpenDomainLaws NormLinearDomainLaws NormClassZeroComposition
  NormDiffeomorphismUP NormDiffeomorphismRestriction EuclideanBlockLinearMaps EuclideanProductBox
  EuclideanSubmanifoldUP SubmanifoldChartsUP SubmanifoldBlockStraightening SubmanifoldBasicLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [standard_straightening_convex_coordinates]: the
    product-neighbourhood argument supporting (1) implies (4) in
    Federer 3.1.19, p. 231, after putting the plane into standard
    linear coordinates. All dimensions and finite classes are included. *)
Theorem standard_straightening_convex_coordinates (R:realType) mu l k
    (B:set (R_n R (mu+l))) b (T C:set (R_n R (mu+l)))
    (s t:R_n R (mu+l)->R_n R (mu+l)) : B b ->
  norm_domain_interior (inner_norm (@euclidean_inner_productP R (mu+l))) T b ->
  is_norm_diffeomorphism (inner_norm_real_norm (@euclidean_inner_productP R (mu+l)))
    (inner_norm_real_norm (@euclidean_inner_productP R (mu+l))) T C s t k ->
  (forall x, T x -> (B x <-> @euclidean_last_block_map R mu l (s x)=0)) ->
  exists U V phi psi,
    norm_domain_interior (inner_norm (@euclidean_inner_productP R (mu+l))) U b /\
    is_inner_convex V /\
    norm_class (inner_norm_real_norm (@euclidean_inner_productP R (mu+l)))
      (inner_norm_real_norm (@euclidean_inner_productP R mu)) U phi k /\
    norm_class (inner_norm_real_norm (@euclidean_inner_productP R mu))
      (inner_norm_real_norm (@euclidean_inner_productP R (mu+l))) V psi k /\
    (forall x, U x -> V (phi x)) /\ (forall u, V u -> U (psi u)) /\
    psi @` V=B `&` U /\ forall u, V u -> phi (psi u)=u.
Proof.
move=>hb hTb hD hplane.
pose X:=R_n R (mu+l); pose Y:=R_n R mu.
pose NX:=inner_norm (@euclidean_inner_productP R (mu+l)).
pose NY:=inner_norm (@euclidean_inner_productP R mu).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (mu+l)).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R mu).
pose p:=@euclidean_first_block_map R mu l.
pose q:=@euclidean_last_block_map R mu l.
pose j:=@euclidean_first_injection_map R mu l.
have hbT:T b:=norm_domain_interior_member hNX hTb.
have hsbC:=@norm_diffeomorphism_maps R X X NX NX hNX hNX T C s t k hD b hbT.
have hqsb:q (s b)=0:=(hplane b hbT).1 hb.
have hc:=norm_class_continuous (norm_diffeomorphism_inverse_class hD).
have [e [he hboxC]]:=@euclidean_product_box_fits R mu l C (s b) (@hc (s b) hsbC).1.
pose P:=@euclidean_product_box R mu l (s b) e.
pose U:=fun x:X=>T x /\ P (s x).
pose V:=fun u:Y=>NY (u-p (s b))<e.
have hopenP x (hx:P x):norm_domain_interior NX P x:=euclidean_product_box_open hx.
have hDU:=@norm_diffeomorphism_target_restriction R X X NX NX hNX hNX T C P s t k
  hD hboxC hopenP.
have hopenU x (hx:U x):norm_domain_interior NX U x.
  have hf:=norm_class_continuous (norm_diffeomorphism_forward_class hDU).
  exact (@hf x hx).1.
have hopenV u (hu:V u):norm_domain_interior NY V u.
  exact (@norm_open_ball_domain_interior R Y NY hNY (p (s b)) e u hu).
have hjV u (hu:V u):P (j u).
  change (is_true (NY (p (j u)-p (s b))<e) /\
    is_true (inner_norm (@euclidean_inner_productP R l) (q (j u)-q (s b))<e)).
  have hpj:p (j u)=u:=@euclidean_first_block_injectionK R mu l u.
  have hqj:q (j u)=0:=@euclidean_last_block_first_injection R mu l u.
  rewrite hpj hqj hqsb subrr inner_norm0.
  by split.
have hpsiU u (hu:V u):U (t (j u)).
  exact (@norm_diffeomorphism_inverse_maps R X X NX NX hNX hNX U P s t k hDU (j u) (hjV u hu)).
have hpbound:=@norm_finite_linear_bounded R X Y NX NY hNX hNY (mu+l)
  (@coordinate_basis R (mu+l)) (@coordinate_basisP R (mu+l)) p.
have hjbound:=@norm_finite_linear_bounded R Y X NY NX hNY hNX mu
  (@coordinate_basis R mu) (@coordinate_basisP R mu) j.
have hphi:=@norm_class_compose_on R X X Y NX NX NY hNX hNX hNY U P s p k
  (fun x hx=>hx.2) (norm_diffeomorphism_forward_class hDU)
  (@norm_class_linear R X Y NX NY hNX hNY P p k hopenP hpbound).
have hpsi:=@norm_class_compose_on R Y X X NY NX NX hNY hNX hNX V P j t k
  hjV (@norm_class_linear R Y X NY NX hNY hNX V j k hopenV hjbound)
  (norm_diffeomorphism_inverse_class hDU).
exists U,V,(fun x=>p (s x)),(fun u=>t (j u)).
split.
- apply: hopenU; split=>//; exact: euclidean_product_box_center he.
split; first exact (@norm_open_ball_convex R Y NY hNY (p (s b)) e).
split=>//; split=>//; split; first by move=>x hx; exact hx.2.1.
split; first exact hpsiU.
have hcan u (hu:V u):s (t (j u))=j u.
  exact (@norm_diffeomorphism_right_inverse R X X NX NX hNX hNX U P s t k hDU (j u) (hjV u hu)).
split; last by move=>u hu; rewrite hcan //; exact (@euclidean_first_block_injectionK R mu l u).
apply/seteqP; split=>x.
- move=>[u hu <-]; split; last exact: hpsiU.
  apply: (hplane _ (hpsiU u hu).1).2.
  rewrite hcan //; exact (@euclidean_last_block_first_injection R mu l u).
- move=>[hBx hUx].
  have hz:q (s x)=0:=(hplane x hUx.1).1 hBx.
  exists (p (s x)); first exact hUx.2.1.
  have hi:j (p (s x))=s x.
    have hd:=@euclidean_block_linear_decomposition R mu l (s x).
    change (s x=j (p (s x))+@euclidean_last_injection_map R mu l (q (s x))) in hd.
    by rewrite hz linear0 addr0 in hd.
  rewrite hi; exact (@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX U P s t k hDU x hUx).
Qed.

(** Source for [submanifold_convex_coordinates]: implication (1)
    to (4), Federer 3.1.19, p. 231. The dimension bound is derived
    at the chosen point, so the empty set stays valid in all dimensions. *)
Theorem submanifold_convex_coordinates (R:realType) n mu k (B:set (R_n R n)) :
  @is_euclidean_submanifold R n mu k B -> @has_convex_coordinate_charts R n mu k B.
Proof.
move=>hB b hb.
have hmn:=submanifold_dimension_at_point hB hb.
have [l hn]:exists l,n=(mu+l)%N by exists (n-mu)%N; rewrite subnKC.
subst n.
have [T [C [s [t [hTb [hD hplane]]]]]]:=submanifold_standard_block_chart hB hb.
exact (@standard_straightening_convex_coordinates R mu l k B b T C s t hb hTb hD hplane).
Qed.
