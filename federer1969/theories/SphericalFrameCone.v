(** Federer (1969), 3.2.47, p. 282: the exact printed
    wedge condition defines an open ambient cone, before intersecting
    the unit sphere. It is linear in the replacing first vector;
    both signs and every positive ambient dimension are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations EuclideanLinearMaps FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP NormClassOneUP
  FamilyUpdate GradedComponents ExteriorAlgebra ExteriorGrading ExteriorIndices
  FiniteExteriorPowers InnerExteriorPositivity ExteriorNorm ExteriorWordReplacementAlgebra
  NormFiniteLinearBound NormRegularity NormRegularityOperations NormOpenDomainLaws
  NormClassZeroTopology SphericalOrthogonalSectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [spherical_frame_input_replacement]: supporting
    equality with replacement of the first ordered wedge factor
    in the exact U of 3.2.47, p. 282. *)
Lemma spherical_frame_input_replacement (R:realType) n
    (e:'I_n.+1->R_n R n.+1) u:
  spherical_frame_input e u=family_with (i:=ord0) [ffun i=>e i] u.
Proof.
apply:funext=>i; rewrite /spherical_frame_input.
case:(eqVneq i ord0)=>[->|hi].
- by rewrite family_with_in.
- rewrite family_with_out ?ffunE //; by rewrite eq_sym.
Qed.

(** Source for [spherical_frame_word]: the actual homogeneous
    top-degree wedge u wedge e_2 wedge ... wedge e_n
    defining U in 3.2.47, p. 282. *)
Definition spherical_frame_word (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (u:R_n R n.+1):
    exterior_power (R_n R n.+1) n.+1:=
  e_lambda (spherical_frame_input e u) (ord_tuple n.+1).

(** Source for [spherical_frame_word_value]: the homogeneous
    word is exactly the printed exterior-algebra product in
    3.2.47, p. 282, not a replacement determinant predicate. *)
Lemma spherical_frame_word_value (R:realType) n
    (e:'I_n.+1->R_n R n.+1) u:
  component_val (spherical_frame_word e u)=
    exterior_word [seq spherical_frame_input e u i|i<-enum 'I_n.+1].
Proof. by rewrite /spherical_frame_word e_lambdaE val_ord_tuple. Qed.

(** Source for [spherical_frame_word_linear]: fixing all
    other factors makes the printed defining wedge linear
    in u, by 1.4.1, p. 17; supporting the
    neighborhood assertion in 3.2.47, p. 282. *)
Lemma spherical_frame_word_linear (R:realType) n
    (e:'I_n.+1->R_n R n.+1):linear (spherical_frame_word e).
Proof.
move=>c u v; rewrite /spherical_frame_word !spherical_frame_input_replacement.
exact (@exterior_word_replacement_linear R (R_n R n.+1) n.+1 e ord0 c u v).
Qed.

(** Source for [spherical_frame_word_map]: the actual linear
    wedge map as a Hom element, supporting the local section
    domain of 3.2.47, p. 282. *)
Definition spherical_frame_word_map (R:realType) n
    (e:'I_n.+1->R_n R n.+1):
    Hom (R_n R n.+1) (exterior_power (R_n R n.+1) n.+1):=
  @HomMap R (R_n R n.+1) (exterior_power (R_n R n.+1) n.+1)
    (spherical_frame_word e) (introT (asboolP _) (spherical_frame_word_linear e)).

(** Source for [spherical_frame_word_smooth]: the actual wedge
    condition in 3.2.47, p. 282, is a smooth map;
    boundedness follows from the finite-dimensional source. *)
Theorem spherical_frame_word_smooth (R:realType) n
    (e:'I_n.+1->R_n R n.+1):
  norm_class_all_orders
    (inner_norm_real_norm (@euclidean_inner_productP R n.+1))
    (inner_norm_real_norm (exterior_inner_productP (euclidean_two_nonzero R)
      (@euclidean_inner_productP R n.+1) n.+1))
    (fun _=>True) (spherical_frame_word e).
Proof.
move=>k; change (norm_class
  (inner_norm_real_norm (@euclidean_inner_productP R n.+1))
  (inner_norm_real_norm (exterior_inner_productP (euclidean_two_nonzero R)
    (@euclidean_inner_productP R n.+1) n.+1))
  (fun _=>True) (spherical_frame_word_map e) k).
apply:norm_class_linear; first by move=>u _; exact:norm_full_domain_interior.
exact (@norm_finite_linear_bounded R (R_n R n.+1) _ _ _
  (inner_norm_real_norm (@euclidean_inner_productP R n.+1))
  (inner_norm_real_norm (exterior_inner_productP (euclidean_two_nonzero R)
    (@euclidean_inner_productP R n.+1) n.+1))
  n.+1 (@coordinate_basis R n.+1) (@coordinate_basisP R n.+1) (spherical_frame_word_map e)).
Qed.

(** Source for [spherical_frame_cone_word_iff]: the original
    nonzero exterior product and the nonzero homogeneous word
    are equivalent, supporting exact-domain openness in 3.2.47,
    p. 282. *)
Lemma spherical_frame_cone_word_iff (R:realType) n
    (e:'I_n.+1->R_n R n.+1) u:
  spherical_frame_cone e u<->spherical_frame_word e u!=0.
Proof.
split=>hNonzero; apply/eqP=>hZero; move/eqP:hNonzero; apply.
- rewrite /spherical_frame_cone -spherical_frame_word_value hZero; exact:linear0.
- apply:val_inj.
  change (component_val (spherical_frame_word e u)=
    component_val (0:exterior_power (R_n R n.+1) n.+1)).
  rewrite spherical_frame_word_value linear0; exact hZero.
Qed.

(** Source for [spherical_frame_cone_interior]: the exact
    printed cone is open at every one of its points;
    supporting the neighborhood U and smooth recurrence in
    3.2.47, p. 282. No hemisphere is excluded. *)
Theorem spherical_frame_cone_interior (R:realType) n
    (e:'I_n.+1->R_n R n.+1) u:
  spherical_frame_cone e u ->
  norm_domain_interior (inner_norm (@euclidean_inner_productP R n.+1))
    (spherical_frame_cone e) u.
Proof.
move=>hCone.
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n.+1).
pose hM:=inner_norm_real_norm (exterior_inner_productP (euclidean_two_nonzero R)
  (@euclidean_inner_productP R n.+1) n.+1).
pose M:=inner_norm (exterior_inner_productP (euclidean_two_nonzero R)
  (@euclidean_inner_productP R n.+1) n.+1).
have hNonzero: spherical_frame_word e u!=0 by apply/spherical_frame_cone_word_iff.
have hPositive:0<M (spherical_frame_word e u).
  by rewrite (real_norm_positive hM.1 hM.2).
have hContinuous:=norm_class_continuous (@spherical_frame_word_smooth R n e 0%N).
have [r [hr hControl]]:=@norm_class_zero_local_control R (R_n R n.+1)
  (exterior_power (R_n R n.+1) n.+1) _ M hN (fun _=>True)
  (spherical_frame_word e) u (M (spherical_frame_word e u)) hContinuous I hPositive.
exists r; split; first exact hr.
move=>v hv; apply/spherical_frame_cone_word_iff; apply/eqP=>hz.
have hSmall:inner_norm (@euclidean_inner_productP R n.+1) ((u+v)-u)<r.
  by rewrite addrAC subrr add0r.
have hDiff:=(hControl (u+v) hSmall).2.
rewrite hz sub0r in hDiff.
change (is_true (M (-spherical_frame_word e u)<M (spherical_frame_word e u))) in hDiff.
have hNeg:M (-spherical_frame_word e u)=M (spherical_frame_word e u).
  exact (@real_seminorm_negate R (exterior_power (R_n R n.+1) n.+1) M hM.1
    (spherical_frame_word e u)).
by rewrite hNeg ltxx in hDiff.
Qed.
