(** Federer (1969), 3.2.32, p. 269: supporting image
    dimension bound in the zero intrinsic-Jacobian branch of
    3.2.22(1), p. 258. Actual source chart coordinates
    preserve the exact partial range. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier SubspaceSums GrassmannAbbreviations
  FiniteCoordinates GrassmannSubspaces EuclideanLinearJacobian LinearRankUP LinearRankAtLeast
  PartialFunctionUP PartialMetricLipschitz PartialExteriorNormUP PartialExteriorNormLaws PartialExteriorChartCoordinates
  PartialLinearChartImage ExteriorJacobianRankZeroIff PartialImageDimensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_partial_exterior_chart_image_dimension]: supporting
    the image-dimension conclusion of Federer 3.2.32, p. 269.
    Isometric coordinates identify the actual intrinsic norm with
    an ordinary exterior norm. Its zero value gives rank below
    mu; inverse coordinate laws identify the exact partial image.
    No off-domain values enter the dimension predicate. *)
Theorem zero_partial_exterior_chart_image_dimension (R:realType) m n v mu
    (D:Hom (R_n R m) (R_n R n)) (H:Hom (R_n R m) (R_n R v))
    (d:partial_function (R_n R n) (R_n R v)):
  injective D ->
  (forall x y,partial_function_graph d x y <->exists a,D a=x /\H a=y) ->
  is_partial_exterior_norm mu d 0 ->is_partial_image_dimension_at_most mu d.
Proof.
move=>hD hGraph hNorm.
have [L [K [Ki [hL [hLK [hIsometry [hLeft hRight]]]]]]]:=
  @partial_exterior_chart_coordinates_exists R m n v mu D H d hD hGraph.
have hZero:euclidean_linear_jacobian mu L=0:=partial_exterior_norm_unique hL hNorm.
have hLow:~linear_rank_at_least L mu:=
  (@euclidean_exterior_jacobian_zero_iff_low_rank R m v mu L).1 hZero.
have [r [hRank hBound]]:=linear_rank_exists L (@coordinate_basisP R v).
have hr:(r<mu)%N.
  rewrite ltnNge; apply/negP=>hAtLeast; apply:hLow.
  exact ((linear_rank_at_leastP mu hRank).2 hAtLeast).
pose P:=@GrassmannSubspace R (R_n R v) r (range_subspace (hom_as_linear L)) hRank.
have hRange:partial_function_range d=range L.
  have hRangeH:=partial_linear_chart_image hGraph.
  change (partial_function_range d=range H) in hRangeH.
  rewrite hRangeH.
  apply/seteqP; split=>y [x _ <-].
  - exists (K x)=>//; exact:hLK.
  - exists (Ki x)=>//; by rewrite -hLK hRight.
exists r,P; split; first exact:ltnW hr.
rewrite hRange; apply/seteqP; split=>y.
- by move=>[x _ <-]; exists x.
- move=>[x hx]; exists x=>//.
Qed.
