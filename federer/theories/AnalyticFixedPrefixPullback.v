(** Federer (1969), 3.4.8(8), p. 330:
    the original Q_m rotations fix every
    original coefficient germ. Apply the
    existing orthonormal coordinate formula and
    pointed pullback composition to the actual
    fixed prefix. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies OrthonormalParseval FiniteDualDimension DualityAnnihilator
  GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  AnalyticGermUP AnalyticGermRing AnalyticPrefixCoordinatesUP AnalyticPrefixCoordinatesSealed
  AnalyticPrefixGermMap AnalyticPrefixGermMapLaws PointedAnalyticPullbackComposition
  AnalyticOrthogonalPullback OrthogonalCoordinateFixing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FixedPrefix.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Hypothesis hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Variable m:nat.
Variable q:@orthogonal_group R X B hB n e he.
Hypothesis hQ:@analytic_suffix_rotation_group R X B hB n e he m q.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation action:=(@orthogonal_element_map R X B hB n e he q).

(** Source for [analytic_fixed_prefix_covector]: every
    original omega_i with i<m is fixed
    by Q_m, as used in the original
    coefficient denominators of 3.4.8(8), p. 330.
    This follows from the existing orthonormal
    dual-coordinate and orthogonal invariance laws. *)
Lemma analytic_fixed_prefix_covector (i:'I_n):
  (i<m)%N ->forall x:X,omega i (action x) = omega i x.
Proof.
move=>hIM x.
have hOmega:omega i = dual_basis he i:=biorthogonal_basis_unique he hDual i.
rewrite hOmega !(@orthonormal_basis_inner_coordinate R X B hB [the finType of 'I_n] e hON he).
have hFixed:=((@orthogonal_coordinate_fixing_membership R X B hB n e he [set k:'I_n|(k<m)%N] q).1 hQ) i hIM.
have hInner:=@orthogonal_element_inner R X B hB n e he q x (e i).
by rewrite hFixed in hInner.
Qed.

(** Source for [analytic_fixed_prefix_projection]: the
    exact original identity p_m q=p_m,
    supporting the coefficient-ring invariance in
    3.4.8(8), p. 330. *)
Lemma analytic_fixed_prefix_projection (hMN:(m<=n)%N) (P:Hom X (R_n R m)):
  is_analytic_prefix_projection omega hMN P ->forall x:X,P (action x) = P x.
Proof.
move=>hP x;apply/ffunP=>i;rewrite !hP.
exact:(@analytic_fixed_prefix_covector (widen_ord hMN i) (ltn_ord i) x).
Qed.

(** Source for [analytic_fixed_prefix_germ]: every
    original Q_m coefficient germ is fixed
    by the original Q_m pullback, as
    used for both denominators and integral
    relations in 3.4.8(8), p. 330.
    The existing pointed composition theorem
    proves the exact germ equation. *)
Theorem analytic_fixed_prefix_germ (hMN:(m<=n)%N):
  forall alpha,@analytic_orthogonal_germ_map R X B hB n e he q
    (@analytic_prefix_germ_map R X NX hNX n e he omega m hMN alpha) =
    @analytic_prefix_germ_map R X NX hNX n e he omega m hMN alpha.
Proof.
pose P:=@AnalyticPrefixCoordinates.projection R X n omega m hMN.
pose E:=@analytic_prefix_germ_map R X NX hNX n e he omega m hMN.
have hP:=@AnalyticPrefixCoordinates.projection_laws R X n omega m hMN.
have hE:=@analytic_prefix_germ_map_specification R X NX hNX n e he omega m hMN.
have hQG:=@analytic_orthogonal_germ_map_specification R X B hB n e he q.
have hComposition:=pointed_analytic_pullback_composes hQG hE.
apply:(pointed_analytic_pullback_map_extensional hComposition hE).
exact:(analytic_fixed_prefix_projection hP).
Qed.
End FixedPrefix.
