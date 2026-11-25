(** Federer (1969), 3.1.21, p. 234: the tangent bundle
    of a mu-dimensional class-(k+1) submanifold is a
    2mu-dimensional class-k submanifold, including k=0. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom ModuleQuotient GrassmannSubspaces GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormDifferentialUP NormRegularity NormDiffeomorphismUP EuclideanSubmanifoldUP
  EuclideanBlockLinearMaps EuclideanBundleUP EuclideanDerivativeLiftLaws EuclideanDerivativeLiftDiffeomorphism
  TangentConeUP GrassmannBlockProduct SubmanifoldStraighteningMembership SubmanifoldStraighteningTangent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [submanifold_tangent_bundle]: the tangent-bundle
    dimension and regularity assertion of Federer 3.1.21,
    p. 234. Ambient products use the existing block
    identification R^n times R^n=R^(n+n); the dimension
    mu+mu is 2mu, with all zero-dimensional cases retained. *)
Theorem submanifold_tangent_bundle (R:realType) n mu k (B:set (R_n R n)) :
  @is_euclidean_submanifold R n mu k.+1 B ->
  @is_euclidean_submanifold R (n+n) (mu+mu) k (@euclidean_tangent_bundle R n B).
Proof.
move=>hB z0 hz0.
pose X:=R_n R n.
pose P:=R_n R (n+n).
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NP:=inner_norm (@euclidean_inner_productP R (n+n)).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNP:=inner_norm_real_norm (@euclidean_inner_productP R (n+n)).
pose p:=@euclidean_first_block_map R n n.
pose q:=@euclidean_last_block_map R n n.
have [T [C [s [t [Z hChart]]]]]:=hB (p z0) hz0.1.
have hSt:=submanifold_straightening_diffeomorphism hChart.
have hTb:=submanifold_straightening_neighbourhood hChart.
have hz0T:=norm_domain_interior_member hNX hTb.
have [D [E [hDs [hDt hLift]]]]:=euclidean_derivative_lift_diffeomorphism hSt.
pose F:=@euclidean_derivative_lift R n s D.
pose G:=@euclidean_derivative_lift R n t E.
pose AT:=fun z:P=>T (p z).
pose AC:=fun z:P=>C (p z).
have [H hH]:=@grassmann_block_product_exists R n mu mu Z Z.
have hmem x (hx:T x):B x <-> grassmann_val Z (s x).
  exact (@submanifold_straightening_membership R n mu k.+1 B T C (p z0) s t Z hChart x hx).
have htan x (hx:T x) (hBx:B x) v :
  norm_tangent_cone NX B x v <-> grassmann_val Z (D x v).
  exact (@submanifold_straightening_tangent R n mu k.+1 B T C (p z0) s t Z D
    (leq0n k) hChart hDs x hx hBx v).
exists AT,AC,F,G,H; constructor.
- exact ((@norm_class_continuous R P P NP NP hNP hNP AT F k
    (norm_diffeomorphism_forward_class hLift) z0 hz0T).1).
- exact hLift.
- apply/seteqP; split=>y.
  + move=>[z [hz hTz] <-].
    have hzB:B (p z):=hz.1.
    split.
    * apply: (hH (F z)).2.
      rewrite euclidean_derivative_lift_base euclidean_derivative_lift_vector.
      split; first exact: (hmem _ hTz).1 hzB.
      exact: (htan _ hTz hzB _).1 hz.2.
    * exact (@norm_diffeomorphism_maps R P P NP NP hNP hNP AT AC F G k hLift z hTz).
  + move=>[hyH hyC].
    pose z:=G y.
    have hzT:AT z:=@norm_diffeomorphism_inverse_maps R P P NP NP hNP hNP AT AC F G k hLift y hyC.
    have hFz:F z=y:=@norm_diffeomorphism_right_inverse R P P NP NP hNP hNP AT AC F G k hLift y hyC.
    have [hyZ hyV]:=(hH y).1 hyH.
    have hbase:s (p z)=p y.
      exact (eq_trans (esym (@euclidean_derivative_lift_base R n s D z)) (congr1 p hFz)).
    have hvector:D (p z) (q z)=q y.
      exact (eq_trans (esym (@euclidean_derivative_lift_vector R n s D z)) (congr1 q hFz)).
    have hzB:B (p z) by apply: (hmem _ hzT).2; by rewrite hbase.
    have hzV:norm_tangent_cone NX B (p z) (q z).
      apply: (htan _ hzT hzB _).2; by rewrite hvector.
    exists z; last exact hFz.
    split; last exact hzT.
    exact (conj hzB hzV).
Qed.
