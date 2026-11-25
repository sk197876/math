(** Federer (1969), 3.2.47, p. 282: independent exact laws
    for the normalized local orthogonal section on the printed set U.
    The actual domain retains both hemispheres. Smoothness, orthogonality
    and the right-inverse identity are conclusions to prove. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  LinearBasis PartialFunctionUP ExteriorAlgebra ExteriorGrading ExteriorIndices AssociatedSubspace IndependentProducts
  PositiveGramSchmidtUP PositiveGramSchmidtUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_frame_input]: the ordered family
    (u,e_2,...,e_n) in the recurrence of 3.2.47, p. 282.
    The zero-based first vector replaces e_1 and all other
    original basis vectors are retained. *)
Definition spherical_frame_input (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (u:R_n R n.+1) (i:'I_n.+1):=
  if i==ord0 then u else e i.

(** Source for [spherical_frame_cone]: the printed nonzero
    exterior product u wedge e_2 wedge ... wedge e_n in
    3.2.47, p. 282, before imposing the unit-sphere condition. *)
Definition spherical_frame_cone (R:realType) n (e:'I_n.+1->R_n R n.+1):=
  [set u|exterior_word [seq spherical_frame_input e u i|i<-enum 'I_n.+1]!=0].

(** Source for [spherical_frame_patch]: the EXACT printed set
    U in 3.2.47, p. 282. The nonzero product permits
    either orientation of the first vector, not only its positive cap. *)
Definition spherical_frame_patch (R:realType) n (e:'I_n.+1->R_n R n.+1):=
  [set u|inner_norm (@euclidean_inner_productP R n.+1) u= 1 /\ spherical_frame_cone e u].

(** Source for [has_spherical_orthogonal_section]: F(u) is
    specified by its exact printed domain and its values on the
    original basis, through the positively normalized recurrence of
    3.2.47, p. 282. No orthogonality, regularity, rank or
    coarea identity is assumed as part of these laws. *)
Definition has_spherical_orthogonal_section (R:realType) n
    (e:'I_n.+1->R_n R n.+1) u (F:Hom (R_n R n.+1) (R_n R n.+1)):=
  spherical_frame_patch e u /\exists v:'I_n.+1->R_n R n.+1,
    is_positive_gram_schmidt (@euclidean_inner_productP R n.+1)
      (spherical_frame_input e u) v /\forall i,F (e i)=v i.

(** Source for [spherical_orthogonal_section_unique]: the
    normalized recurrence in 3.2.47, p. 282, and the
    actual basis values determine F(u) uniquely. No chosen
    basis-coordinate implementation is exposed. *)
Lemma spherical_orthogonal_section_unique (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e) u F G:
  has_spherical_orthogonal_section e u F ->
  has_spherical_orthogonal_section e u G ->F=G.
Proof.
move=>[_ [v [hv hF]]] [_ [w [hw hG]]].
have hSame:=positive_gram_schmidt_unique hv hw.
apply:hom_ext=>x.
apply:(@basis_linear_ext R [the choiceType of 'I_n.+1]
  (R_n R n.+1) e he (R_n R n.+1) (hom_as_linear F) (hom_as_linear G))=>i.
by rewrite !hom_as_linearE hF hG hSame.
Qed.

(** Source for [is_spherical_orthogonal_section_graph]: the map
    F with domain exactly U in 3.2.47, p. 282, specified
    by its actual normalized basis values. Existence is a theorem;
    differentiability and the inverse identity are not assumed. *)
Record is_spherical_orthogonal_section_graph (R:realType) n
    (e:'I_n.+1->R_n R n.+1)
    (F:partial_function (R_n R n.+1) (Hom (R_n R n.+1) (R_n R n.+1))):Prop:={
  (** Source for [spherical_section_domain]: the printed exact
      domain U of F in 3.2.47, p. 282. *)
  spherical_section_domain:partial_function_domain F=spherical_frame_patch e;
  (** Source for [spherical_section_value]: the exact normalized
      basis-value graph defining F in 3.2.47, p. 282. *)
  spherical_section_value:forall u L,partial_function_graph F u L<->
    has_spherical_orthogonal_section e u L
}.
