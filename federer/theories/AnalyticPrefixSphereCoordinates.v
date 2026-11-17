(** Federer (1969), 3.4.8(6), pp. 328–329:
    the original prefix sphere is isometric to the
    unit sphere in R^p. The original projection
    and basis inclusion provide both actual inverses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP RealNormUP InnerProductUP InnerNorm InnerMetric
  Bilinear LinearBasis FiniteDualDimension Annihilator OrthonormalFamilies OrthonormalParseval
  InnerNormalization GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct CoordinateProjection
  AnalyticPrefixCoordinatesUP AnalyticPrefixBasisValues AnalyticPrefixCoordinateLaws
  AnalyticPrefixOrthogonalProjection OrthogonalMaps AnalyticPrefixSphereAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Coordinates.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Variable p:nat.
Variable hPN:(p<=n)%N.
Variable P:Hom X (R_n R p).
Variable S:Hom (R_n R p) X.
Hypothesis hP:is_analytic_prefix_projection omega hPN P.
Hypothesis hS:is_analytic_prefix_section e hPN S.
Local Notation Y:=(R_n R p).
Local Notation C:=(@euclidean_inner_product R p).
Local Notation hC:=(@euclidean_inner_productP R p).

(** Source for [analytic_prefix_section_norm]: the original
    prefix inclusion is isometric, supporting the sphere
    identification in 3.4.8(6), p. 328. *)
Lemma analytic_prefix_section_norm (y:Y):inner_norm hB (S y) = inner_norm hC y.
Proof.
have hOrthogonal:=@analytic_prefix_inclusion_orthogonal R X B hB n e hON p hPN S hS.
exact:(@orthogonal_map_norm R Y X C B hC hB (hom_as_linear S) hOrthogonal y).
Qed.

(** Source for [analytic_prefix_section_tail_orthogonal]: the
    original prefix inclusion is orthogonal to every
    fixed tail vector, 3.4.8(6), p. 328. *)
Lemma analytic_prefix_section_tail_orthogonal (y:Y) (i:'I_n):
  (p<=i)%N ->B (S y) (e i) = 0.
Proof.
move=>hPI.
have hE:y = \sum_j (dual_basis (@coordinate_basisP R p) j y:R)*: @coordinate_basis R p j.
  exact:basis_vector_expansion.
rewrite hE linear_sum /=.
rewrite (big_morph (fun z:X=>B z (e i))
  (fun u v=>@bilDl R X X R^o B (inner_bilinear hB) u v (e i))
  (@bil0l R X X R^o B (inner_bilinear hB) (e i))).
apply:big1=>j _.
rewrite (linZ (hom_linear S)) (bilZl (inner_bilinear hB)) hS hON.
have hDiff:widen_ord hPN j != i.
  apply/eqP=>hEqual.
  have hValues:(j:nat) = (i:nat):=congr1 (fun t:'I_n=>(t:nat)) hEqual.
  have hSmall:(i<p)%N by rewrite -hValues;exact:ltn_ord.
  have hFalse:=leq_ltn_trans hPI hSmall;by rewrite ltnn in hFalse.
by rewrite (negbTE hDiff) scaler0.
Qed.

(** Source for [analytic_prefix_section_projection_fixed]:
    every vector perpendicular to the original tail
    equals the inclusion of its prefix coordinates,
    3.4.8(6), p. 328. *)
Lemma analytic_prefix_section_projection_fixed (x:X):
  (forall i:'I_n,(p<=i)%N ->B x (e i) = 0) ->S (P x) = x.
Proof.
move=>hTail.
pose T:=hom_comp S P.
have hOnBasis i:(dual_basis he i x:R)*:T (e i) = (dual_basis he i x:R)*:e i.
  case:(ltnP i p)=>hIP.
  - pose j:'I_p:=Ordinal hIP.
    have hIndex:widen_ord hPN j = i by apply:val_inj.
    rewrite /T hom_compE -hIndex
      (@analytic_prefix_basis_inside R X n e omega p hPN P hP hDual j) hS;by [].
  - have hZero:dual_basis he i x = 0.
      rewrite (@orthonormal_basis_inner_coordinate R X B hB (Finite.clone 'I_n _) e hON he i x).
      exact:hTail.
    by rewrite hZero !scale0r.
have hExpansion:=basis_vector_expansion he x.
have hImage:T x = \sum_i (dual_basis he i x:R)*:T (e i).
  rewrite {1}hExpansion (big_morph T (linD (hom_linear T)) (lin0 (hom_linear T))).
  apply:eq_bigr=>i _;exact:(linZ (hom_linear T)).
change (T x = x);rewrite hImage [RHS]hExpansion.
apply:eq_bigr=>i _;exact:hOnBasis.
Qed.

(** Source for [analytic_prefix_sphere_image]: the original
    S is exactly the included unit sphere in
    R^p, 3.4.8(6), p. 328. *)
Lemma analytic_prefix_sphere_image:
  (S @` [set y:Y|inner_norm hC y = 1]) = @analytic_prefix_unit_sphere R X B hB n e p.
Proof.
apply/seteqP;split=>x.
- move=>[y hY <-];split.
  + by rewrite analytic_prefix_section_norm.
  + move=>i hi;exact:analytic_prefix_section_tail_orthogonal.
- move=>[hUnit hTail];exists (P x).
  + change (inner_norm hC (P x) = 1).
    rewrite -analytic_prefix_section_norm (analytic_prefix_section_projection_fixed hTail);exact:hUnit.
  + exact:analytic_prefix_section_projection_fixed.
Qed.
End Coordinates.
