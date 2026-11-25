(** Federer (1969), 3.2.47, p. 283: the
    actual r-th exterior norm of evaluation on a tangent
    containing the horizontal lifts is 2^(-r/2). All
    Hilbert Hom pairings are evaluated from the rank-one
    lift; the quotient and its adjoint are proved locally. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp ring.
From Federer Require Import Hom TensorUP Bilinear ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerProductRestriction
  InnerNorm OrthogonalMaps AdjointUP LinearBasis EuclideanLinearMaps
  EuclideanHomInnerCharts EuclideanGramDifferentialAlgebra EuclideanStiefelHalfNormalization
  SphericalHorizontalLift SphericalHorizontalLiftLinear SphericalOrthogonalOrbitDifferential
  ScaledOrthogonalQuotientExteriorNorm InnerExteriorPositivity ExteriorMaps OperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [spherical_horizontal_quotient_exterior_norm]:
    the restricted r-Jacobian computed in the last display
    of 3.2.47, p. 283. This linear supporting
    theorem requires the actual Gram tangent and lift
    containments, which the geometric preimage theorem discharges.
    No Jacobian or adapted frame is a premise. *)
Theorem spherical_horizontal_quotient_exterior_norm (R:realType) N r
    (g:Hom (R_n R N) (R_n R N)) (c:R_n R N)
    (T:subspace (Hom (R_n R N) (R_n R N))) (U:G (R_n R N) r):
  is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear g) ->
  euclidean_inner_product c c= 1 ->
  (forall v,grassmann_val U v ->euclidean_inner_product (g c) v=0) ->
  (forall w,T w ->euclidean_gram_differential g w=0) ->
  (forall w,T w ->grassmann_val U (w c)) ->
  (forall v,grassmann_val U v ->T (spherical_horizontal_lift g c v)) ->
  let hT:=restricted_inner_productP (@euclidean_hom_inner_productP R N N) T in
  is_operator_norm (exterior_inner_productP (euclidean_two_nonzero R) hT r)
    (exterior_inner_productP (euclidean_two_nonzero R) (@euclidean_inner_productP R N) r)
    (exterior_power_map (hom_as_linear (hom_comp (spherical_orthogonal_orbit c)
      (hom_of_linear (subspace_inclusion T)))) r) (((Num.sqrt (2:R))^-1)^+r).
Proof.
move=>hg hc hPerp hGram hEval hLift hT.
pose V:=R_n R N.
pose H:=Hom V V.
pose S:=grassmann_val U.
pose X:=subspace_space T.
pose Y:=subspace_space S.
pose hU:=restricted_inner_productP (@euclidean_inner_productP R N) S.
pose s:=(Num.sqrt (2:R))^-1.
have [hs hScale]:=euclidean_stiefel_half_normalization R.
have hLiftMember v (hv:S v):T (s*:spherical_horizontal_lift g c v).
  exact (subspace_scale s (@hLift v hv)).
pose lift0:=fun u:Y=>@subspace_lift R H T (s*:spherical_horizontal_lift g c (subspace_val u))
  (@hLiftMember (subspace_val u) (subspace_valP u)).
have hLiftLinear:linear lift0.
  move=>a x y; apply:subspace_val_injective.
  change (s*:spherical_horizontal_lift g c (a*:subspace_val x+subspace_val y)=
    a*:(s*:spherical_horizontal_lift g c (subspace_val x))+
      s*:spherical_horizontal_lift g c (subspace_val y)).
  rewrite (@spherical_horizontal_lift_linear R N g c a (subspace_val x) (subspace_val y))
    scalerDr !scalerA [s*a]mulrC; reflexivity.
pose L:Hom Y X:=@HomMap R Y X lift0 (introT (asboolP _) hLiftLinear).
have hEvalMember w (hw:T w):S ((2*s)*:(w c)).
  exact (subspace_scale (2*s) (@hEval w hw)).
pose eval0:=fun w:X=>@subspace_lift R V S ((2*s)*:(subspace_val w c))
  (@hEvalMember (subspace_val w) (subspace_valP w)).
have hEvalLinear:linear eval0.
  move=>a x y; apply:subspace_val_injective.
  change ((2*s)*:(a*:(subspace_val x c)+subspace_val y c)=
    a*:((2*s)*:(subspace_val x c))+(2*s)*:(subspace_val y c)).
  by rewrite scalerDr !scalerA [2*s*a]mulrC.
pose P:Hom X Y:=@HomMap R X Y eval0 (introT (asboolP _) hEvalLinear).
pose A:=@subspace_inclusion R V S.
pose F:=hom_comp (spherical_orthogonal_orbit c) (hom_of_linear (subspace_inclusion T)).
have hL:is_orthogonal_map (@restricted_inner_product R V (@euclidean_inner_product R N) S)
    (@restricted_inner_product R H (@euclidean_hom_inner_product R N N) T) (hom_as_linear L).
  move=>u v.
  change (euclidean_hom_inner_product (s*:spherical_horizontal_lift g c (subspace_val u))
    (s*:spherical_horizontal_lift g c (subspace_val v))=
    euclidean_inner_product (subspace_val u) (subspace_val v)).
  rewrite (bilZl (inner_bilinear (@euclidean_hom_inner_productP R N N)))
    (bilZr (inner_bilinear (@euclidean_hom_inner_productP R N N)))
    (@spherical_horizontal_lift_pairing R N g (spherical_horizontal_lift g c (subspace_val v))
      c (subspace_val u) hg (@spherical_horizontal_lift_tangent R N g c (subspace_val v) hg))
    (@spherical_horizontal_lift_evaluation R N g c (subspace_val v) hc
      (@hPerp _ (subspace_valP v))).
  have hFactor:s*(s*(2*euclidean_inner_product (subspace_val u) (subspace_val v)))=
      (2*s*s)*euclidean_inner_product (subspace_val u) (subspace_val v) by ring.
  change (s*(s*(2*euclidean_inner_product (subspace_val u) (subspace_val v)))=
    euclidean_inner_product (subspace_val u) (subspace_val v)).
  by rewrite hFactor hScale mul1r.
have hP:is_adjoint (@restricted_inner_product R V (@euclidean_inner_product R N) S)
    (@restricted_inner_product R H (@euclidean_hom_inner_product R N N) T)
    (hom_as_linear L) (hom_as_linear P).
  move=>u w.
  change (euclidean_inner_product (subspace_val u) ((2*s)*:(subspace_val w c))=
    euclidean_hom_inner_product (s*:spherical_horizontal_lift g c (subspace_val u)) (subspace_val w)).
  rewrite (bilZr (inner_bilinear (@euclidean_inner_productP R N)))
    (bilZl (inner_bilinear (@euclidean_hom_inner_productP R N N)))
    (@spherical_horizontal_lift_pairing R N g (subspace_val w) c (subspace_val u) hg
      (@hGram _ (subspace_valP w))).
  change ((2*s)*euclidean_inner_product (subspace_val u) (subspace_val w c)=
    s*(2*euclidean_inner_product (subspace_val u) (subspace_val w c))).
  ring.
have hA:is_orthogonal_map (@restricted_inner_product R V (@euclidean_inner_product R N) S)
    (@euclidean_inner_product R N) A by move=>u v.
have hF w:F w=s*:A (P w).
  change (subspace_val w c=s*:((2*s)*:(subspace_val w c))).
  have hCoefficient:s*(2*s)= 1.
    have hEq:s*(2*s)= 2*s*s by ring.
    by rewrite hEq.
  by rewrite scalerA hCoefficient scale1r.
have [b hb]:=grassmann_proof U.
exact (@scaled_orthogonal_quotient_top_exterior_norm R (euclidean_two_nonzero R)
  Y X V _ _ _ hU hT (@euclidean_inner_productP R N) r b hb
  (hom_as_linear L) (hom_as_linear P) A (hom_as_linear F) s hL hP hA (ltW hs) hF).
Qed.
