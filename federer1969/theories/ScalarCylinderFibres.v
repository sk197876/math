(** Federer (1969), 3.2.33, p. 270: strict increase of g
    fixes precisely the first mu+1 coordinates of every fibre. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RealOpenIntervals EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanSliceDifferentials
  EuclideanOpenUnitCube ScalarCylinderMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_strict_interval_injective]: supporting the
    fibre cubes in Federer 3.2.33, p. 270. Strict increase
    on the actual open interval gives injectivity there; no
    injectivity off the original scalar domain is assumed. *)
Lemma scalar_strict_interval_injective (R:realType) (g:R->R):
  (forall u v,real_open_interval 0 1 u ->real_open_interval 0 1 v ->u<v ->g u<g v) ->
  forall u v,real_open_interval 0 1 u ->real_open_interval 0 1 v ->g u=g v ->u=v.
Proof.
move=>hStrict u v hu hv he.
case:(ltP u v)=>[huv|hvu].
  by have:=hStrict u v hu hv huv; rewrite he ltxx.
case:(ltP v u)=>[hvu2|huv].
  by have:=hStrict v u hv hu hvu2; rewrite he ltxx.
apply/eqP; by rewrite eq_le huv hvu.
Qed.

(** Source for [scalar_cylinder_fibre_prefix]: f(x)=f(y)
    precisely when the first mu+1 source coordinates agree,
    for points in W, Federer 3.2.33, p. 270. The proof
    uses only the independent coordinate laws and actual strict
    increase of g; both empty blocks are retained. *)
Theorem scalar_cylinder_fibre_prefix (R:realType) mu k (g:R->R)
    (F:R_n R ((mu+1)+k)->R_n R (mu+1)):
  is_scalar_cylinder_map g F ->
  (forall u v,real_open_interval 0 1 u ->real_open_interval 0 1 v ->u<v ->g u<g v) ->
  forall x y,euclidean_open_unit_cube x ->euclidean_open_unit_cube y ->
    (F x=F y <->@euclidean_first_block R (mu+1) k x=euclidean_first_block y).
Proof.
move=>hF hStrict x y hx hy; split.
- move=>hEq; apply/ffunP=>i; rewrite /euclidean_first_block !ffunE.
  rewrite -(splitK i); case:(split i)=>j.
  + have h:=congr1 (fun z:R_n R (mu+1)=>z (lshift 1 j)) hEq.
    by rewrite !(scalar_cylinder_first_coordinates hF) in h.
  + rewrite (ord1 j).
    apply:(scalar_strict_interval_injective hStrict).
    * have /andP [h0 h1]:=hx (lshift k (rshift mu ord0)); by split.
    * have /andP [h0 h1]:=hy (lshift k (rshift mu ord0)); by split.
    * have h:=congr1 (fun z:R_n R (mu+1)=>z (rshift mu ord0)) hEq.
      by rewrite !(scalar_cylinder_last_coordinate hF) in h.
- move=>hEq; apply/ffunP=>i; rewrite -(splitK i); case:(split i)=>j.
  + rewrite !(scalar_cylinder_first_coordinates hF).
    have h:=congr1 (fun z:R_n R (mu+1)=>z (lshift 1 j)) hEq.
    by rewrite /euclidean_first_block !ffunE in h.
  + rewrite (ord1 j) !(scalar_cylinder_last_coordinate hF).
    congr (g _).
    have h:=congr1 (fun z:R_n R (mu+1)=>z (rshift mu ord0)) hEq.
    by rewrite /euclidean_first_block !ffunE in h.
Qed.

(** Source for [scalar_cylinder_fibre_cube]: every nonempty
    fibre in W is exactly a translate of the k-dimensional
    unit cube, where k=m-mu-1, Federer 3.2.33, p. 270.
    The equality includes all points of the original domain,
    rather than an almost-everywhere or measurable-hull substitute. *)
Theorem scalar_cylinder_fibre_cube (R:realType) mu k (g:R->R)
    (F:R_n R ((mu+1)+k)->R_n R (mu+1)):
  is_scalar_cylinder_map g F ->
  (forall u v,real_open_interval 0 1 u ->real_open_interval 0 1 v ->u<v ->g u<g v) ->
  forall x,euclidean_open_unit_cube x ->
    [set y|euclidean_open_unit_cube y /\F y=F x]=
    (fun z=>euclidean_block_join (@euclidean_first_block R (mu+1) k x,z)) @`
      (@euclidean_open_unit_cube R k).
Proof.
move=>hF hStrict x hx.
have hPrefixCube:euclidean_open_unit_cube (@euclidean_first_block R (mu+1) k x).
  by move=>i; rewrite /euclidean_first_block ffunE; exact:hx.
apply/seteqP; split=>y.
- move=>[hy hEq].
  have hPrefix:euclidean_first_block y=euclidean_first_block x:=
    (scalar_cylinder_fibre_prefix hF hStrict hy hx).1 hEq.
  exists (@euclidean_last_block R (mu+1) k y).
  + by move=>i; rewrite /euclidean_last_block ffunE; exact:hy.
  + rewrite -hPrefix; exact:euclidean_block_splitK.
- move=>[z hz <-]; split.
  + exact:(euclidean_open_unit_cube_join _ _).2 (conj hPrefixCube hz).
  + apply:(scalar_cylinder_fibre_prefix hF hStrict _ hx).2.
    * exact:(euclidean_open_unit_cube_join _ _).2 (conj hPrefixCube hz).
    * exact:(congr1 fst (euclidean_block_joinK (@euclidean_first_block R (mu+1) k x,z))).
Qed.
