(** Federer (1969), 3.2.48, p. 285: the actual Cartesian tangent
    plane and its isometric carrier. Its sum dimension is proved by
    the actual injective product inclusion; no rank or basis is assumed
    for a tangent plane beyond its original Grassmann laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier SubspaceSums
  GrassmannSubspaces GrassmannAbbreviations InnerProductUP InnerProductRestriction
  ProductInner OrthogonalMaps LinearBasis ProductFiniteBasis LinearRankUP LinearInjectiveRank
  CartesianTopExteriorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [grassmann_cartesian_product]: the source product
    tangent plane of 3.2.48, p. 285, has the sum of the two actual
    tangent dimensions. The natural Cartesian carrier is isometrically
    bijective to this plane. Empty coordinate blocks remain literal. *)
Theorem grassmann_cartesian_product (R:realType) (V W:lmodType R)
    BV BW (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW)
    n m (v:'I_n->V) (w:'I_m->W) (hv:is_basis v) (hw:is_basis w)
    r s (S:G V r) (T:G W s):
  exists P:G [the lmodType R of (V*W)%type] (r+s)%N,
    (forall z,grassmann_val P z <->grassmann_val S z.1 /\grassmann_val T z.2) /\
    let U:lmodType R:=[the lmodType R of (subspace_space (grassmann_val S)*subspace_space (grassmann_val T))%type] in
    exists (i:Hom U (subspace_space (grassmann_val P))) (j:Hom (subspace_space (grassmann_val P)) U),
      cancel i j /\cancel j i /\
      is_orthogonal_map
        (product_inner (restricted_inner_productP hV (grassmann_val S)) (restricted_inner_productP hW (grassmann_val T)))
        (@restricted_inner_product R _ (product_inner hV hW) (grassmann_val P)) (hom_as_linear i) /\
      forall z,subspace_val (i z)=(subspace_val z.1,subspace_val z.2).
Proof.
pose U:lmodType R:=[the lmodType R of (subspace_space (grassmann_val S)*subspace_space (grassmann_val T))%type].
pose Z:lmodType R:=[the lmodType R of (V*W)%type].
pose F:=cartesian_linear_hom (hom_of_linear (subspace_inclusion (grassmann_val S)))
  (hom_of_linear (subspace_inclusion (grassmann_val T))).
have hF z:F z=(subspace_val z.1,subspace_val z.2).
  case:z=>x y; by rewrite /F cartesian_linear_homE.
have hInjective:injective F.
  move=>[x y] [x' y'] hEq; rewrite !hF in hEq.
  have hx:x=x':=subspace_val_injective (congr1 fst hEq).
  have hy:y=y':=subspace_val_injective (congr1 snd hEq).
  by rewrite hx hy.
have [b hb]:=grassmann_proof S.
have [c hc]:=grassmann_proof T.
have hRank:=@linear_injective_rank R U Z (r+s)%N (cartesian_basis b c) (cartesian_basisP hb hc)
  (n+m)%N (cartesian_basis v w) (cartesian_basisP hv hw) F hInjective.
pose P:=@GrassmannSubspace R Z (r+s)%N (range_subspace (hom_as_linear F)) hRank.
have hPlane z:grassmann_val P z <->grassmann_val S z.1 /\grassmann_val T z.2.
  split.
  - move=>[u hzu]; change (z=F u) in hzu; rewrite hzu hF.
    split; exact:subspace_valP.
  - move=>[hzS hzT].
    exists (@subspace_lift R V (grassmann_val S) z.1 hzS,@subspace_lift R W (grassmann_val T) z.2 hzT).
    change (z=F (@subspace_lift R V (grassmann_val S) z.1 hzS,
      @subspace_lift R W (grassmann_val T) z.2 hzT)); rewrite hF /=.
    exact (surjective_pairing z).
have hMember z:grassmann_val P (F z).
  exists z; reflexivity.
pose f:=fun z:U=>@subspace_lift R Z (grassmann_val P) (F z) (hMember z).
have hf:linear f.
  move=>a z z'; apply:subspace_val_injective.
  change (F (a*:z+z')=a*:F z+F z'); exact (hom_linear F a z z').
pose i:Hom U (subspace_space (grassmann_val P)):=@HomMap R _ _ f (introT (asboolP _) hf).
pose hU:=product_inner_productP (restricted_inner_productP hV (grassmann_val S))
  (restricted_inner_productP hW (grassmann_val T)).
pose hP:=restricted_inner_productP (product_inner_productP hV hW) (grassmann_val P).
have hOrth:is_orthogonal_map
    (product_inner (restricted_inner_productP hV (grassmann_val S)) (restricted_inner_productP hW (grassmann_val T)))
    (@restricted_inner_product R Z (product_inner hV hW) (grassmann_val P)) (hom_as_linear i).
  move=>z z'.
  change (product_inner hV hW (F z) (F z')=
    product_inner (restricted_inner_productP hV (grassmann_val S)) (restricted_inner_productP hW (grassmann_val T)) z z').
  by rewrite !hF !product_innerE.
have hi:injective (hom_as_linear i):=orthogonal_map_injective hU hP hOrth.
have hs:forall u:subspace_space (grassmann_val P),exists z:U,i z=u.
  move=>u; have [z hz]:=subspace_valP u.
  exists z; apply:subspace_val_injective.
  change (F z=subspace_val u); exact (esym hz).
pose j:Hom (subspace_space (grassmann_val P)) U:=hom_of_linear
  (GRing.Linear.clone _ _ _ _ (@linear_inverse R U (subspace_space (grassmann_val P)) (hom_as_linear i) hi hs) _).
exists P; split; first exact hPlane.
exists i,j; split.
- exact (@linear_inverseKV R U (subspace_space (grassmann_val P)) (hom_as_linear i) hi hs).
- split.
  + exact (@linear_inverseK R U (subspace_space (grassmann_val P)) (hom_as_linear i) hi hs).
  + split; first exact hOrth.
    move=>z; exact (hF z).
Qed.
