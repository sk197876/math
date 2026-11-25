(** Federer (1969), 3.2.33, p. 270: actual rank of
    the displayed differential and its exact low-rank locus. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanOneCoordinate
  LinearRankUP LinearRankTransport LinearInjectiveRank ScalarCylinderMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_cylinder_zero_coefficient_rank]: the
    actual differential has rank mu on g'= 0,
    supporting X in Federer 3.2.33, p. 270.
    Its image is exactly the first mu-dimensional coordinate
    plane; the proof includes the zero plane for mu= 0. *)
Theorem scalar_cylinder_zero_coefficient_rank (R:realType) mu k
    (L:Hom (R_n R ((mu+1)+k)) (R_n R (mu+1))):
  is_scalar_cylinder_map (fun _=>0) L ->has_linear_rank L mu.
Proof.
move=>hL.
pose J:=@euclidean_first_injection_map R mu 1.
pose P (x:R_n R ((mu+1)+k)):=@euclidean_first_block R mu 1 (@euclidean_first_block R (mu+1) k x).
have hInj:injective J.
  move=>u v he.
  have h:=congr1 (@euclidean_first_block R mu 1) he.
  change (euclidean_first_block (@euclidean_first_injection R mu 1 u)=
    euclidean_first_block (@euclidean_first_injection R mu 1 v)) in h.
  by rewrite !euclidean_first_block_injectionK in h.
have hJ:has_linear_rank J mu:=@linear_injective_rank R (R_n R mu) (R_n R (mu+1))
  mu (@coordinate_basis R mu) (@coordinate_basisP R mu)
  (mu+1) (@coordinate_basis R (mu+1)) (@coordinate_basisP R (mu+1)) J hInj.
have hValue x:L x=J (P x).
  apply/ffunP=>i; rewrite -(splitK i); case:(split i)=>a.
  - rewrite (scalar_cylinder_first_coordinates hL).
    change (x (lshift k (lshift 1 a))=
      @euclidean_first_injection R mu 1 (P x) (lshift 1 a)).
    by rewrite /euclidean_first_injection euclidean_block_join_left /P /euclidean_first_block !ffunE.
  - rewrite (ord1 a) (scalar_cylinder_last_coordinate hL).
    change (0= @euclidean_first_injection R mu 1 (P x) (rshift mu ord0)).
    by rewrite /euclidean_first_injection euclidean_block_join_right ffunE.
apply:(@linear_same_image_rank R (R_n R mu) (R_n R ((mu+1)+k)) (R_n R (mu+1))
  J L (mu+1) (@coordinate_basis R (mu+1)) (@coordinate_basisP R (mu+1)) mu hJ).
- move=>u; exists (@euclidean_first_injection R (mu+1) k (J u)); rewrite hValue.
  congr (J _).
  change (euclidean_first_block (euclidean_first_block
    (@euclidean_first_injection R (mu+1) k (@euclidean_first_injection R mu 1 u)))=u).
  by rewrite !euclidean_first_block_injectionK.
- move=>x; exists (P x); exact:(esym (hValue x)).
Qed.

(** Source for [scalar_cylinder_nonzero_coefficient_rank]: away
    from g'= 0 the differential has rank mu+1, supporting
    the exact equality for X in Federer 3.2.33, p. 270.
    Division by the actual nonzero coefficient proves surjectivity;
    no rank or determinant premise is added. *)
Theorem scalar_cylinder_nonzero_coefficient_rank (R:realType) mu k c
    (L:Hom (R_n R ((mu+1)+k)) (R_n R (mu+1))):
  is_scalar_cylinder_map (fun t=>c*t) L ->c!= 0 ->has_linear_rank L (mu+1).
Proof.
move=>hL hC.
have hSurj (y:R_n R (mu+1)):exists x,L x=y.
  pose v:=euclidean_block_join (@euclidean_first_block R mu 1 y,
    euclidean_one_embed (y (rshift mu ord0)/c)).
  exists (@euclidean_first_injection R (mu+1) k v).
  apply/ffunP=>i; rewrite -(splitK i); case:(split i)=>a.
  - rewrite (scalar_cylinder_first_coordinates hL) /euclidean_first_injection
      euclidean_block_join_left /v euclidean_block_join_left /euclidean_first_block ffunE.
    reflexivity.
  - rewrite (ord1 a) (scalar_cylinder_last_coordinate hL) /euclidean_first_injection
      euclidean_block_join_left /v euclidean_block_join_right /euclidean_one_embed ffunE.
    by rewrite mulrC divfK.
pose I:=hom_of_linear (linear_id (R_n R (mu+1))).
have hI:has_linear_rank I (mu+1).
  apply:(@linear_injective_rank R (R_n R (mu+1)) (R_n R (mu+1))
    (mu+1) (@coordinate_basis R (mu+1)) (@coordinate_basisP R (mu+1))
    (mu+1) (@coordinate_basis R (mu+1)) (@coordinate_basisP R (mu+1)) I).
  by move=>x y h; exact h.
apply:(@linear_same_image_rank R (R_n R (mu+1)) (R_n R ((mu+1)+k)) (R_n R (mu+1))
  I L (mu+1) (@coordinate_basis R (mu+1)) (@coordinate_basisP R (mu+1)) (mu+1) hI).
- move=>y; exact:hSurj.
- move=>x; by exists (L x).
Qed.

(** Source for [scalar_cylinder_low_rank_iff_zero]: the exact
    low-rank source equality in Federer 3.2.33, p. 270,
    before substituting the already proved zero set of g'.
    This uses actual linear image dimensions and retains mu= 0. *)
Theorem scalar_cylinder_low_rank_iff_zero (R:realType) mu k c
    (L:Hom (R_n R ((mu+1)+k)) (R_n R (mu+1))):
  is_scalar_cylinder_map (fun t=>c*t) L ->
  ((exists r,has_linear_rank L r /\(r<=mu)%N)<->c= 0).
Proof.
move=>hL; split.
- move=>[r [hR hr]].
  case:(eqVneq c 0)=>[hZero|hNonzero]; first exact hZero.
  have hTop:=scalar_cylinder_nonzero_coefficient_rank hL hNonzero.
  have he:=linear_rank_unique hR hTop.
  by rewrite he addn1 ltnn in hr.
- move=>hZero.
  have hZ:is_scalar_cylinder_map (fun _=>0) L.
    constructor; first exact:(scalar_cylinder_first_coordinates hL).
    move=>x; have h:=scalar_cylinder_last_coordinate hL x.
    by rewrite hZero mul0r in h.
  exists mu; split; first exact:(scalar_cylinder_zero_coefficient_rank hZ).
  exact:leqnn.
Qed.
