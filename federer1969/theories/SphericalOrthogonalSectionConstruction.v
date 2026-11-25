(** Federer (1969), 3.2.47, p. 282: private existence
    for the independently specified normalized local section.
    The construction supplies basis interpolation only; regularity
    and transformation properties remain separate proof obligations. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  LinearBasis BasisInterpolation PartialFunctionUP FiniteIndependence
  SimpleWordIndependence PositiveGramSchmidtUP PositiveGramSchmidt
  SphericalOrthogonalSectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_section_value_exists]: actual positively
    normalized basis interpolation gives F(u) for each point
    of U in 3.2.47, p. 282. *)
Lemma spherical_section_value_exists (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e) u:
  spherical_frame_patch e u ->exists L,has_spherical_orthogonal_section e u L.
Proof.
move=>hPatch.
have hIndependent:finite_independent (spherical_frame_input e u).
  exact (@nonzero_word_independent R (R_n R n.+1) n.+1
    (spherical_frame_input e u) hPatch.2).
pose v:=positive_gram_schmidt_family (@euclidean_inner_productP R n.+1) hIndependent.
exists (hom_of_linear (basis_interpolation he v)); split; first exact hPatch.
exists v; split; first exact:positive_gram_schmidt_laws.
move=>i; rewrite hom_of_linearE; exact:basis_interpolationE.
Qed.

(** Source for [spherical_orthogonal_section_graph_exists]:
    existence of the exact-domain section F of 3.2.47,
    p. 282, from positive recurrence existence and uniqueness.
    The original domain U and its two hemispheres remain. *)
Theorem spherical_orthogonal_section_graph_exists (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e):
  exists F,is_spherical_orthogonal_section_graph e F.
Proof.
pose F:=@Build_partial_function (R_n R n.+1) (Hom (R_n R n.+1) (R_n R n.+1))
  (fun u L=>has_spherical_orthogonal_section e u L)
  (fun u L M hL hM=>@spherical_orthogonal_section_unique R n e he u L M hL hM).
exists F; constructor.
- apply/seteqP; split=>u.
  + by move=>[L [hPatch _]].
  + move=>hPatch; exact (@spherical_section_value_exists R n e he u hPatch).
- by move=>u L.
Qed.
