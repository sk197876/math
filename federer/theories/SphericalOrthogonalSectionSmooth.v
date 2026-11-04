(** Federer (1969), 3.2.47, p. 282: existence of a
    smooth ambient representative for the exact normalized local section.
    Auxiliary choices remain existential; smoothness is proved from
    the independent positive recurrence, never from a choice implementation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP OrthogonalMaps OrthogonalBasisCriteria EuclideanHomInnerCharts InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP
  NormClassOneUP LinearBasis FiniteIndependence PartialFunctionUP
  OrthonormalFamilies OrthonormalisationUP IndependentProducts SimpleWordIndependence
  PositiveGramSchmidtUP PositiveGramSchmidt PositiveGramSchmidtSmooth
  EuclideanFrameAssemblySmooth SphericalFrameCone SphericalOrthogonalSectionUP
  SphericalOrthogonalSection SphericalOrthogonalSectionValues
  NormRegularity NormRegularityOperations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_frame_input_norm_class]: every input
    of the printed recurrence is either the original u or a
    fixed e_i, hence smooth on its exact open cone;
    supporting 3.2.47, p. 282. *)
Lemma spherical_frame_input_norm_class (R:realType) n
    (e:'I_n.+1->R_n R n.+1) i k:
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R n.+1))
    (inner_norm_real_norm (@euclidean_inner_productP R n.+1))
    (spherical_frame_cone e) (fun u=>spherical_frame_input e u i) k.
Proof.
pose V:=R_n R n.+1.
pose N:=inner_norm (@euclidean_inner_productP R n.+1).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n.+1).
have hOpen u (hu:spherical_frame_cone e u):norm_domain_interior N (spherical_frame_cone e) u.
  exact:spherical_frame_cone_interior hu.
case:(eqVneq i ord0)=>[->|hi].
- pose L:=hom_of_linear (linear_id V).
  have hBound:norm_bounded_linear N N L.
    exists 1; split; first exact:ler01.
    move=>u; change (N u<=1*N u); by rewrite mul1r.
  have hClass:=@norm_class_linear R V V N N hN hN (spherical_frame_cone e) L k hOpen hBound.
  apply:(norm_class_domain_agreement _ hClass)=>u hu.
  by rewrite /spherical_frame_input eqxx.
- have hClass:=@norm_class_constant R V V N N hN hN (spherical_frame_cone e) (e i) k hOpen.
  apply:(norm_class_domain_agreement _ hClass)=>u hu.
  by rewrite /spherical_frame_input (negbTE hi).
Qed.

(** Source for [spherical_positive_frame_family_exists]: independent
    positive recurrence values exist on every point of the actual
    open cone in 3.2.47, p. 282. A total auxiliary
    family may be chosen, but no outside value is a geometric claim. *)
Lemma spherical_positive_frame_family_exists (R:realType) n
    (e:'I_n.+1->R_n R n.+1):
  exists v:R_n R n.+1->'I_n.+1->R_n R n.+1,
    forall u,spherical_frame_cone e u ->
      is_positive_gram_schmidt (@euclidean_inner_productP R n.+1)
        (spherical_frame_input e u) (v u).
Proof.
have hEach u:exists v:'I_n.+1->R_n R n.+1,
    spherical_frame_cone e u ->is_positive_gram_schmidt (@euclidean_inner_productP R n.+1)
      (spherical_frame_input e u) v.
  case:(pselect (spherical_frame_cone e u))=>[hCone|hOutside].
  - have hIndependent:finite_independent (spherical_frame_input e u).
      exact (@nonzero_word_independent R (R_n R n.+1) n.+1
        (spherical_frame_input e u) hCone).
    exists (positive_gram_schmidt_family (@euclidean_inner_productP R n.+1) hIndependent).
    move=>_; exact:positive_gram_schmidt_laws.
  - exists (fun _=>0); by move=>/hOutside.
exists (fun u=>projT1 (cid (hEach u))).
move=>u hu; exact (projT2 (cid (hEach u)) hu).
Qed.

(** Source for [spherical_orthogonal_section_smooth_representative]: the
    actual F in 3.2.47, p. 282, is differentiable
    of every finite class. The proof supplies an ambient cone
    representative and discharges every recurrence and nonzero-denominator
    premise. Its original partial graph is preserved exactly. *)
Theorem spherical_orthogonal_section_smooth_representative (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e)
    (hON:orthonormal_family (@euclidean_inner_product R n.+1) e):
  exists F:R_n R n.+1->Hom (R_n R n.+1) (R_n R n.+1),
    norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R n.+1))
      (inner_norm_real_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
      (spherical_frame_cone e) F /\
    (forall u,spherical_frame_cone e u ->
      is_orthogonal_map (@euclidean_inner_product R n.+1)
        (@euclidean_inner_product R n.+1) (hom_as_linear (F u))) /\
    (forall u L,partial_function_graph (spherical_orthogonal_section he) u L ->F u=L).
Proof.
have [v hv]:=@spherical_positive_frame_family_exists R n e.
pose F:=fun u=>euclidean_frame_assembly e (v u).
have hValues u i:F u (e i)=v u i.
  exact (@euclidean_frame_assemblyE R n.+1 n.+1 e (v u) hON i).
have hOrthonormal u (hu:spherical_frame_cone e u):
    orthonormal_family (@euclidean_inner_product R n.+1) (v u).
  exact:orthonormalisation_orthonormal (positive_gram_schmidt_orthonormalisation (hv u hu)).
exists F; split.
- move=>k.
  have hComponents i:norm_class
      (inner_norm_real_norm (@euclidean_inner_productP R n.+1))
      (inner_norm_real_norm (@euclidean_inner_productP R n.+1))
      (spherical_frame_cone e) (fun u=>v u i) k.
    exact (@positive_gram_schmidt_norm_class R (R_n R n.+1) (R_n R n.+1)
      _ (inner_norm_real_norm (@euclidean_inner_productP R n.+1))
      _ (@euclidean_inner_productP R n.+1) n.+1 (spherical_frame_cone e)
      (fun i u=>spherical_frame_input e u i) (fun i u=>v u i) k hv
      (fun i=>@spherical_frame_input_norm_class R n e i k) i).
  exact (@euclidean_frame_assembly_norm_class R (R_n R n.+1) _
    (inner_norm_real_norm (@euclidean_inner_productP R n.+1)) n.+1 n.+1 e
    (spherical_frame_cone e) (fun i u=>v u i) k
    (fun u hu=>spherical_frame_cone_interior hu) hComponents).
- split.
  + move=>u hu.
    apply:(@orthogonal_map_basis_criterion R (R_n R n.+1) (R_n R n.+1)
      _ _ (@euclidean_inner_productP R n.+1) (@euclidean_inner_productP R n.+1)
      n.+1 e he hON (hom_as_linear (F u))).
    move=>i j; rewrite !hom_as_linearE !hValues; exact: hOrthonormal u hu i j.
  + move=>u L hGraph.
    have [hPatch _]:=proj1 (@spherical_orthogonal_section_graph R n e he u L) hGraph.
    apply:(@spherical_orthogonal_section_unique R n e he u (F u) L).
    * split; first exact hPatch.
      exists (v u); split; first exact:hv u hPatch.2.
      exact:hValues.
    * exact:proj1 (spherical_orthogonal_section_graph he u L) hGraph.
Qed.
