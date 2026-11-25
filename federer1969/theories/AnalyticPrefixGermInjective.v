(** Federer (1969), 3.4.8(1),(10), pp. 326,
    330: the original prefix pullback is
    injective. Apply the existing pointed
    retraction theorem to its actual analytic
    section. No germ construction is unfolded. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness AnalyticGermRing AnalyticPrefixCoordinatesSealed
  AnalyticPrefixCoordinateLaws AnalyticPrefixMapRegularity AnalyticPrefixGermMap AnalyticPrefixGermMapLaws
  PointedAnalyticPullbackSealed PointedAnalyticPullbackRetraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_prefix_germ_map_injective]: the
    original Q_m is an isomorphic copy
    of O_0(R^m), used when p restricted
    to Q_m is a monomorphism in
    3.4.8(10), p. 330. The original
    coordinate section gives the actual
    germ left inverse, including m=0. *)
Theorem analytic_prefix_germ_map_injective (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o) (hDual:forall i k,omega i (e k) = if i==k then 1 else 0)
  m (hMN:(m<=n)%N):
  injective (@analytic_prefix_germ_map R X NX hNX n e he omega m hMN).
Proof.
pose Y:=R_n R m.
pose NY:=inner_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose P:=@AnalyticPrefixCoordinates.projection R X n omega m hMN.
pose S:=@AnalyticPrefixCoordinates.inclusion R X n e m hMN.
pose E:=@analytic_prefix_germ_map R X NX hNX n e he omega m hMN.
have hP:=@AnalyticPrefixCoordinates.projection_laws R X n omega m hMN.
have hS:=@AnalyticPrefixCoordinates.inclusion_laws R X n e m hMN.
have hSection:=@analytic_prefix_projection_section R X n e omega m hMN P S hDual hP hS.
have hAnalytic:=(@analytic_prefix_inclusion_analytic R X NX hNX m S) 0 Logic.I.
pose T:=@PointedAnalyticPullback.map R Y X NY NX hNY hNX setT S 0 0 hAnalytic (linear0 S).
have hT:=@PointedAnalyticPullback.laws R Y X NY NX hNY hNX setT S 0 0 hAnalytic (linear0 S).
have hE:=@analytic_prefix_germ_map_specification R X NX hNX n e he omega m hMN.
have hCancel:=@pointed_analytic_germ_pullback_retraction R X Y NX NY hNX hNY 0 0 P S E T hE hT hSection.
exact:can_inj hCancel.
Qed.
