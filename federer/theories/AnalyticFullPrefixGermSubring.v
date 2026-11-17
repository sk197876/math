(** Federer (1969), 3.4.8(1),(11), pp. 326,
    333: the full coordinate subring Q_n
    is the whole original analytic germ ring.
    Reuse the existing pointed pullback retraction
    theorem and the original dual-basis equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP LinearBasis GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness AnalyticGermRing AnalyticPrefixCoordinatesSealed
  AnalyticPrefixCoordinateLaws AnalyticPrefixBasisValues AnalyticPrefixMapRegularity AnalyticPrefixGermMap
  AnalyticPrefixGermMapLaws PointedAnalyticPullbackSealed PointedAnalyticPullbackRetraction
  AnalyticPrefixGermSubring AnalyticCoordinateSubringFamilyUP AnalyticCoordinateSubringFamilySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_full_prefix_germ_subring]:
    a nonzero original ideal has a
    nonzero member in Q_n, used in
    3.4.8(11), p. 333. The full
    coordinate inverse proves the stronger exact
    equality Q_n=O_0(X). *)
Theorem analytic_full_prefix_germ_subring (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e)
    (omega:'I_n->Hom X R^o)
    (hDual:forall i j,omega i (e j) = if i==j then 1 else 0):
  @AnalyticCoordinateSubringFamily.value R X NX hNX n e he omega n = setT.
Proof.
pose Y:=R_n R n.
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose P:=@AnalyticPrefixCoordinates.projection R X n omega n (leqnn n).
pose S:=@AnalyticPrefixCoordinates.inclusion R X n e n (leqnn n).
pose E:=@analytic_prefix_germ_map R X NX hNX n e he omega n (leqnn n).
have hP:=@AnalyticPrefixCoordinates.projection_laws R X n omega n (leqnn n).
have hS:=@AnalyticPrefixCoordinates.inclusion_laws R X n e n (leqnn n).
have hSP:forall x,S (P x) = x.
  apply:(@basis_linear_ext R 'I_n X e he X (hom_as_linear (hom_comp S P)) (linear_id X))=>i.
  have hPi:P (e i) = @coordinate_basis R n i.
    apply/ffunP=>j;rewrite hP hDual /coordinate_basis ffunE.
    have hWiden:widen_ord (leqnn n) j = j by apply:val_inj.
    by rewrite hWiden eq_sym.
  rewrite hom_as_linearE hom_compE hPi hS.
  have hWiden:widen_ord (leqnn n) i = i by apply:val_inj.
  by rewrite hWiden.
have hAnalytic:=(@analytic_prefix_inclusion_analytic R X NX hNX n S) 0 Logic.I.
pose T:=@PointedAnalyticPullback.map R Y X NY NX hNY hNX setT S 0 0 hAnalytic (linear0 S).
have hT:=@PointedAnalyticPullback.laws R Y X NY NX hNY hNX setT S 0 0 hAnalytic (linear0 S).
have hE:=@analytic_prefix_germ_map_specification R X NX hNX n e he omega n (leqnn n).
have hCancel:=@pointed_analytic_germ_pullback_retraction R Y X NY NX hNY hNX 0 0
  S P T E hT hE hSP.
have hQ:=@AnalyticCoordinateSubringFamily.laws R X NX hNX n e he omega.
rewrite (analytic_coordinate_subring_family_member hQ (leqnn n)).
apply/seteqP;split=>alpha _;first exact:Logic.I.
apply/analytic_prefix_germ_subring_membership;exists (T alpha);exact:hCancel alpha.
Qed.
