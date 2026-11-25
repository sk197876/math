(** Federer (1969), 3.4.2(8), pp. 315–316: use separate
    finite subdivisions along p(Z) and its perpendicular complement. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra ring.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric RealNormUP NormMetric RealPower
  EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry EqualCoordinateCubeGridUP
  EqualCoordinateCubeGridLaws MetricDiameterUP MetricDiameter MetricScaleEnvelopeUP
  HausdorffLengthUP MetricRealPowerCost RealPowerCutoffFiniteCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_two_scale_grid_cover]: the finite
    anisotropic covering estimate in 3.4.2(8), pp. 315–316.
    Flat increments control the first block and a Lipschitz bound
    controls the second. Each image piece has diameter at most
    eps*(a*h)^lambda+M*b*j. Empty pieces need no chosen centre.
    This is a supporting estimate; the actual manifold and all
    subdivision parameters are supplied later from the original hypotheses. *)
Theorem critical_two_scale_grid_cover (R:realType) a b alpha beta
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (F:R_n R a->R_n R b->Y)
    (P:set (R_n R a*R_n R b))
    (u:R_n R a) (v:R_n R b) (r h j eps M lambda delta:R)
    (QA:set (inner_metric_space (@euclidean_inner_productP R a)))
    (QB:set (inner_metric_space (@euclidean_inner_productP R b)))
    (A:coordinate_cube_grid_indices a alpha->
      set (inner_metric_space (@euclidean_inner_productP R a)))
    (B:coordinate_cube_grid_indices b beta->
      set (inner_metric_space (@euclidean_inner_productP R b))):
  is_euclidean_coordinate_cube u r QA ->is_euclidean_coordinate_cube v r QB ->
  is_equal_coordinate_cube_grid alpha u h A ->
  is_equal_coordinate_cube_grid beta v j B ->
  r=alpha%:R*h ->r=beta%:R*j ->
  0<=eps ->0<=M ->0<lambda ->a%:R*h<=delta ->
  (forall z,P z ->QA z.1 /\QB z.2) ->
  (forall c w x,P (c,w) ->QA x ->
    inner_norm (@euclidean_inner_productP R a) (x-c)<=delta ->
    NY (F x w-F c w)<=eps*real_power
      (inner_norm (@euclidean_inner_productP R a) (x-c)) lambda) ->
  (forall x w z,QA x ->QB w ->QB z ->
    NY (F x w-F x z)<=M*inner_norm (@euclidean_inner_productP R b) (w-z)) ->
  exists S:([the finType of (coordinate_cube_grid_indices a alpha*
      coordinate_cube_grid_indices b beta)%type])->
      set (real_norm_metric_space hNY),
    (fun z=>F z.1 z.2) @` P `<=` \bigcup_i S i /\
    forall i,(extended_metric_diameter (S i)<=
      (eps*real_power (a%:R*h) lambda+M*b%:R*j)%:E)%E.
Proof.
move=>hQA hQB hA hB hSideA hSideB hEps hM hLambda hDelta hP hFlat hLip.
pose I:finType:=[the finType of (coordinate_cube_grid_indices a alpha*
  coordinate_cube_grid_indices b beta)%type].
pose S (i:I):set (real_norm_metric_space hNY):=
  (fun z:R_n R a*R_n R b=>F z.1 z.2) @`
    [set z|P z /\A i.1 z.1 /\B i.2 z.2].
exists S;split.
- move=>y [z hz <-].
  have [hza hzb]:=hP z hz.
  have hBoxA k:u k<=z.1 k<=u k+alpha%:R*h.
    rewrite -hSideA;exact:(hQA.2 z.1).1 hza k.
  have hBoxB k:v k<=z.2 k<=v k+beta%:R*j.
    rewrite -hSideB;exact:(hQB.2 z.2).1 hzb k.
  have [ia hia]:=equal_coordinate_grid_covers_box hA hBoxA.
  have [ib hib]:=equal_coordinate_grid_covers_box hB hBoxB.
  exists (ia,ib);first by [].
  exists z;last reflexivity.
  by repeat split.
- move=>i;apply:(metric_diameter_least (extended_metric_diameter_specification (S i))).
  + rewrite lee_fin;apply:addr_ge0.
    * exact:mulr_ge0 hEps (real_power_nonnegative _ _).
    * exact:mulr_ge0 (mulr_ge0 hM (ler0n R b)) hB.2.1.
  + move=>y z [s [hs [hsa hsb]] <-] [c [hc [hca hcb]] <-].
    rewrite lee_fin real_norm_metric_distanceE.
    have [hSA hSB]:=hP s hs.
    have [hCA hCB]:=hP c hc.
    have hFirst:inner_norm (@euclidean_inner_productP R a) (s.1-c.1)<=a%:R*h.
      exact:(@coordinate_cube_distance_bound R a _ h _
        (equal_coordinate_grid_cell_cube hA i.1) s.1 c.1 hsa hca).
    have hSecond:inner_norm (@euclidean_inner_productP R b) (s.2-c.2)<=b%:R*j.
      exact:(@coordinate_cube_distance_bound R b _ j _
        (equal_coordinate_grid_cell_cube hB i.2) s.2 c.2 hsb hcb).
    have hCenter:P (c.1,c.2) by rewrite -surjective_pairing.
    have hOne:=hFlat c.1 c.2 s.1 hCenter hSA (le_trans hFirst hDelta).
    have hPower:=@real_power_monotone R
      (inner_norm (@euclidean_inner_productP R a) (s.1-c.1)) (a%:R*h) lambda
      (inner_norm_nonnegative _ _) hFirst hLambda.
    have hOneBound:=le_trans hOne (ler_wpM2l hEps hPower).
    have hTwo:=hLip s.1 s.2 c.2 hSA hSB hCB.
    have hTwoBound:=le_trans hTwo (ler_wpM2l hM hSecond).
    have hEq:F s.1 s.2-F c.1 c.2=
      (F s.1 s.2-F s.1 c.2)+(F s.1 c.2-F c.1 c.2) by rewrite addrA subrK.
    rewrite hEq;apply:(le_trans (real_seminorm_triangle hNY.1 _ _)).
    have hProduct:M*(b%:R*j)=M*b%:R*j by ring.
    rewrite hProduct in hTwoBound.
    have hSum:=lerD hTwoBound hOneBound;lra.
Qed.
