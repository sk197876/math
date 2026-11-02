(** Federer (1969), 3.2.33, p. 270: the printed cylinder
    map is smooth on its actual open unit-cube domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness RealNormUP RealOpenIntervals NormDifferentialUP NormFiniteLinearBound
  NormRegularity NormRegularityOperations EuclideanBlockCoordinates EuclideanBlockLinear
  EuclideanBlockLinearMaps EuclideanBlockNorms EuclideanOneCoordinate EuclideanOneNormDifferential
  EuclideanOpenUnitCube ScalarCylinderMapUP ScalarCylinderLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_cylinder_smooth]: f has class infinity,
    Federer 3.2.33, p. 270. The independent coordinate laws
    identify f with a bounded linear first block plus a
    bounded linear inclusion composed with g and one coordinate.
    The book's proved class calculus supplies every order on W;
    no smooth extension of g outside T is required. *)
Theorem scalar_cylinder_smooth (R:realType) mu k (g:R->R)
    (F:R_n R ((mu+1)+k)->R_n R (mu+1)):
  is_scalar_cylinder_map g F ->
  norm_class_all_orders (scalar_absolute_value_norm R) (scalar_absolute_value_norm R)
    (real_open_interval 0 1) g ->
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R ((mu+1)+k)))
    (inner_norm_real_norm (@euclidean_inner_productP R (mu+1)))
    (@euclidean_open_unit_cube R ((mu+1)+k)) F.
Proof.
move=>hF hg.
pose X:=R_n R ((mu+1)+k).
pose Y:=R_n R (mu+1).
pose NX:=inner_norm (@euclidean_inner_productP R ((mu+1)+k)).
pose NY:=inner_norm (@euclidean_inner_productP R (mu+1)).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R ((mu+1)+k)).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R (mu+1)).
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose W:=@euclidean_open_unit_cube R ((mu+1)+k).
pose p (x:X):R^o:=x (lshift k (rshift mu ord0)).
have hpLin:linear p by move=>c x y; rewrite /p !ffunE.
pose P:=@HomMap R X R^o p (introT (asboolP _) hpLin).
have hpBound:norm_bounded_linear NX N P.
  exact:(@norm_finite_linear_bounded R X R^o NX N hNX hN ((mu+1)+k)
    (@coordinate_basis R ((mu+1)+k)) (@coordinate_basisP R ((mu+1)+k)) P).
pose j (s:R^o):Y:=@euclidean_last_injection R mu 1 (euclidean_one_embed s).
have hjLin:linear j.
  move=>c s t.
  have hE:euclidean_one_embed (c*s+t)=c*:euclidean_one_embed s+euclidean_one_embed t.
    by apply/ffunP=>i; rewrite /euclidean_one_embed !ffunE.
  rewrite /j hE.
  exact:(@euclidean_last_injection_linear R mu 1 c (euclidean_one_embed s) (euclidean_one_embed t)).
pose J:=@HomMap R R^o Y j (introT (asboolP _) hjLin).
have hjBound:norm_bounded_linear N NY J.
  exists 1; split; first exact:ler01.
  move=>s; change (is_true (NY (j s)<= 1*`|s|)).
  by rewrite /NY /j euclidean_last_injection_norm euclidean_one_norm_coordinate /euclidean_one_embed ffunE mul1r.
have [A [hA hABound]]:=@scalar_cylinder_linear_exists R mu k 0.
have hImage x (hx:W x):real_open_interval 0 1 (P x).
  have /andP [h0 h1]:=hx (lshift k (rshift mu ord0)); by split.
have hopen x (hx:W x):norm_domain_interior NX W x:=euclidean_open_unit_cube_interior hx.
move=>q.
have hP:=@norm_class_linear R X R^o NX N hNX hN W P q hopen hpBound.
have hJ:=@norm_class_linear R R^o Y N NY hN hNY (fun _=>True) J q
  (fun t _=>ltac:(exists 1; split; first exact:ltr01; by move=>v hv))
  hjBound.
have hG:=@norm_class_compose_on R X R^o R^o NX N N hNX hN hN
  W (real_open_interval 0 1) P g q hImage hP (hg q).
have hLast:=@norm_class_compose_on R X R^o Y NX N NY hNX hN hNY
  W (fun _=>True) (fun x=>g (P x)) J q
  (fun x hx=>Logic.I) hG hJ.
have hFirst:=@norm_class_linear R X Y NX NY hNX hNY W A q hopen hABound.
have hSum:=@norm_class_add R X Y NX NY hNX hNY W A (fun x=>J (g (P x))) q hFirst hLast.
apply:(@norm_class_domain_agreement R X Y NX NY hNX hNY W
  (fun x=>A x+J (g (P x))) F q _ hSum)=>x hx.
apply/ffunP=>i; rewrite -(splitK i); case:(split i)=>a.
- rewrite ffunE (scalar_cylinder_first_coordinates hA) (scalar_cylinder_first_coordinates hF).
  change (x (lshift k (lshift 1 a))+j (g (p x)) (lshift 1 a)=x (lshift k (lshift 1 a))).
  by rewrite /j /euclidean_last_injection euclidean_block_join_left ffunE addr0.
- rewrite (ord1 a) ffunE (scalar_cylinder_last_coordinate hA) (scalar_cylinder_last_coordinate hF) mul0r add0r.
  change (j (g (p x)) (rshift mu ord0)=g (x (lshift k (rshift mu ord0)))).
  by rewrite /j /p /euclidean_last_injection euclidean_block_join_right /euclidean_one_embed ffunE.
Qed.
