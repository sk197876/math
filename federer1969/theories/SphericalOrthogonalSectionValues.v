(** Federer (1969), 3.2.47, p. 282: the actual normalized
    section is orthogonal, maps the first original basis vector to
    the original unit u, and equals the identity at the base point. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP ExteriorAlgebra PartialFunctionUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerNormalization OrthonormalFamilies OrthonormalisationUP OrthogonalMaps
  OrthogonalBasisCriteria LinearBasis FiniteBasisCriterion FiniteBasisComparison EuclideanLinearMaps
  IndependentProducts PositiveGramSchmidtUP PositiveGramSchmidtOrthonormal
  SphericalOrthogonalSectionUP SphericalOrthogonalSection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_section_first_vector]: Phi(F(u))=u
    in 3.2.47, p. 282. The original u may lie in
    either hemisphere of the exact printed U. *)
Theorem spherical_section_first_vector (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e) u F:
  partial_function_graph (spherical_orthogonal_section he) u F ->F (e ord0)=u.
Proof.
move=>/(spherical_orthogonal_section_graph he u F) [hPatch [v [hv hF]]].
have hUnit:inner_norm (@euclidean_inner_productP R n.+1)
    (spherical_frame_input e u ord0)= 1.
  by rewrite /spherical_frame_input eqxx; exact:hPatch.1.
rewrite hF (positive_gram_schmidt_unit_first hv hUnit).
by rewrite /spherical_frame_input eqxx.
Qed.

(** Source for [spherical_section_orthogonal]: the actual F(u)
    belongs to O(n) as asserted in 3.2.47, p. 282.
    It follows from the proved normalized family, rather than
    being an orthogonality axiom in the section specification. *)
Theorem spherical_section_orthogonal (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e)
    (hON:orthonormal_family (@euclidean_inner_product R n.+1) e) u F:
  partial_function_graph (spherical_orthogonal_section he) u F ->
  is_orthogonal_map (@euclidean_inner_product R n.+1)
    (@euclidean_inner_product R n.+1) (hom_as_linear F).
Proof.
move=>/(spherical_orthogonal_section_graph he u F) [_ [v [hv hF]]].
apply:(@orthogonal_map_basis_criterion R (R_n R n.+1) (R_n R n.+1)
  (@euclidean_inner_product R n.+1) (@euclidean_inner_product R n.+1)
  (@euclidean_inner_productP R n.+1) (@euclidean_inner_productP R n.+1)
  n.+1 e he hON (hom_as_linear F)).
move=>i j; rewrite !hom_as_linearE !hF.
exact ((orthonormalisation_orthonormal (positive_gram_schmidt_orthonormalisation hv)) i j).
Qed.

(** Source for [spherical_section_base_point]: the original
    orthonormal basis beginning with c is fixed by F(c),
    as follows from the recurrence of 3.2.47, p. 282.
    This also proves that c belongs to the actual domain U. *)
Theorem spherical_section_base_point (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e)
    (hON:orthonormal_family (@euclidean_inner_product R n.+1) e):
  partial_function_graph (spherical_orthogonal_section he) (e ord0)
    (hom_of_linear (linear_id (R_n R n.+1))).
Proof.
have hInput:spherical_frame_input e (e ord0)=e.
  apply:funext=>i; rewrite /spherical_frame_input.
  by case:(eqVneq i ord0)=>[->|hi].
have hPatch:spherical_frame_patch e (e ord0).
  split; first exact (@orthonormal_norm1 R (R_n R n.+1)
    (@euclidean_inner_product R n.+1) (@euclidean_inner_productP R n.+1)
    (Finite.clone 'I_n.+1 _) e hON ord0).
  change (exterior_word [seq spherical_frame_input e (e ord0) i|i<-enum 'I_n.+1]!=0).
  have hWords:[seq spherical_frame_input e (e ord0) i|i<-enum 'I_n.+1]=
      [seq e i|i<-enum 'I_n.+1].
    apply:eq_map=>i; exact (congr1 (fun f=>f i) hInput).
  rewrite hWords.
  exact (@independent_word_nonzero R (euclidean_two_nonzero R)
    (R_n R n.+1) n.+1 e (finite_basis_independent he)).
apply/(spherical_orthogonal_section_graph he).
split; first exact hPatch.
exists e; split.
- rewrite hInput.
  exact (@orthonormal_positive_gram_schmidt R (R_n R n.+1)
    (@euclidean_inner_product R n.+1) (@euclidean_inner_productP R n.+1) n.+1 e hON).
- by move=>i; rewrite hom_of_linearE.
Qed.
