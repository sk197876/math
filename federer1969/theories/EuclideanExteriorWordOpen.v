(** Federer (1969), 3.2.28(2), printed p. 265:
    Q is open onto its simple-unit image. The erratum,
    book p. 265 line 3, deletes the compactness phrase.
    Use the actual open orbit laws of both homogeneous
    spaces, with the proved equivariance of Q. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanLinearMaps InnerMetric InnerNormedTopology
  InnerExteriorPositivity ExteriorGrading ExteriorMaps ExteriorMapScaling
  ExteriorNorm FiniteExteriorPowers OrthogonalMaps
  OrthogonalInjectionSpaces OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  EuclideanOrthogonalInvariantMeasures SimpleVectorAction SimpleVectorHomogeneous
  HomeomorphismUP HomogeneousSpaceUP HomogeneousEquivariantOpen EuclideanExteriorWordSmooth
  EuclideanExteriorWordEvaluation EuclideanExteriorWordImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OpenExteriorMap.
Variable R:realType.
Variables m n:nat.
Local Notation hBm:=(@euclidean_inner_productP R m).
Local Notation hBn:=(@euclidean_inner_productP R n).
Local Notation hbm:=(@coordinate_basisP R m).
Local Notation hbn:=(@coordinate_basisP R n).
Local Notation OI:=(set_type (@euclidean_orthogonal_injections R n m)).
Local Notation U:=(set_type (unit_simple_set hBn m)).

(** Source for [euclidean_frame_unit_exterior_member]: the
    image inclusion for Q in Federer 3.2.28(2), p. 264,
    expressed in the existing homogeneous simple-unit space. *)
Lemma euclidean_frame_unit_exterior_member (f:OI):
  unit_simple_set hBn m (euclidean_exterior_word_map (orthogonal_injection_map f)).
Proof.
have [hs hn]:=euclidean_exterior_word_frame_unit (orthogonal_injection_map_orthogonal f).
split; last exact hs.
by rewrite inner_norm_topologyE.
Qed.

(** Source for [euclidean_frame_unit_exterior_map]: Q as
    a map from O(n,m) into the actual simple-unit subspace,
    Federer 3.2.28(2), p. 264. Only the previously
    proved image-inclusion laws certify the subtype value. *)
Definition euclidean_frame_unit_exterior_map (f:OI):U:=
  exist _ (euclidean_exterior_word_map (orthogonal_injection_map f):
    inner_metric_space (exterior_inner_productP (euclidean_two_nonzero R) hBn m))
    (mem_set (euclidean_frame_unit_exterior_member f)).

(** Source for [euclidean_frame_unit_exterior_open]: openness
    of Q onto Go(n,m), Federer 3.2.28(2), p. 265.
    Actual source and target open orbit laws prove it;
    this applies the erratum deletion on p. 265 line 3.
    Positive m retains the oriented simple-unit realization. *)
Theorem euclidean_frame_unit_exterior_open:
  (0<m)%N ->(m<=n)%N ->is_open_map euclidean_frame_unit_exterior_map.
Proof.
move=>hm hmn.
have [mul [inv [e hO]]]:=orthogonal_group_restriction_exists hBn hbn.
have hSource:=@orthogonal_injections_homogeneous R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n) hBm hBn
  m (@coordinate_basis R m) n (@coordinate_basis R n) hbm hbn mul inv e hO.
have hTarget:=@unit_simple_homogeneous R (R_n R n) (@euclidean_inner_product R n)
  hBn n (@coordinate_basis R n) hbn m hm mul inv e hO.
have [f hf]:=@euclidean_orthogonal_injection_exists R n m hmn.
pose x:=orthogonal_injection_of hBm hBn hbm hf.
apply:(@homogeneous_equivariant_open_map _ OI U mul
  (orthogonal_injection_action hBm hBn hbm hbn)
  (unit_simple_action hBn hbn m) euclidean_frame_unit_exterior_map x hSource hTarget).
move=>s z; apply:val_inj.
change (euclidean_exterior_word_map
    (hom_comp (orthogonal_element_map s) (orthogonal_injection_map z))=
  exterior_power_map (hom_as_linear (orthogonal_element_map s)) m
    (euclidean_exterior_word_map (orthogonal_injection_map z))).
rewrite !euclidean_exterior_word_mapE exterior_power_map_composition.
have he:hom_as_linear (hom_comp (orthogonal_element_map s) (orthogonal_injection_map z))=1
    linear_comp (hom_as_linear (orthogonal_element_map s))
      (hom_as_linear (orthogonal_injection_map z)) by move=>v.
exact:(@exterior_power_map_ext R (R_n R m) (R_n R n)
  (hom_as_linear (hom_comp (orthogonal_element_map s) (orthogonal_injection_map z)))
  (linear_comp (hom_as_linear (orthogonal_element_map s))
    (hom_as_linear (orthogonal_injection_map z))) he m
  (e_lambda (@coordinate_basis R m) (ord_tuple m))).
Qed.
End OpenExteriorMap.
