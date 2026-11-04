(** Federer (1969), 3.2.47, pp. 282–283: the
    actual isotropy at a coordinate unit vector is O(n-1).
    Restriction and identity extension are inverse orthogonal maps;
    the actual Frobenius distances are preserved. Empty transverse
    blocks are included, so the isotropy of O(1) has one element. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerNorm CoordinateProjection
  EuclideanBlockCoordinates EuclideanBlockLinear EuclideanBlockLinearMaps
  EuclideanBlockExtensionUP EuclideanBlockExtension EuclideanBlockHomDifference
  EuclideanHomInnerCharts OrthogonalMaps SphericalOrthogonalProductAlgebra ConcatenatedFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_block_join_decomposition]: supporting
    exact direct-sum coordinates in the isotropy identification
    of 3.2.47, p. 282; the block isomorphism is
    the existing one from 2.6.5, p. 120. *)
Lemma euclidean_block_join_decomposition (R:realType) a b
    (u:R_n R a) (v:R_n R b):
  euclidean_block_join (u,v)=euclidean_first_injection b u+euclidean_last_injection a v.
Proof.
apply/ffunP=>i.
rewrite /euclidean_first_injection /euclidean_last_injection /euclidean_block_join
  !ffunE /concatenate_family.
case:(split i)=>j /=; by rewrite !ffunE ?addr0 ?add0r.
Qed.

(** Source for [spherical_coordinate_pole]: the first standard
    unit vector, used temporarily to identify I with
    O(n-1) in 3.2.47, p. 282. *)
Definition spherical_coordinate_pole (R:realType) n:R_n R (1+n):=
  @coordinate_basis R (1+n) (lshift n (ord0:'I_1)).

(** Source for [spherical_coordinate_restriction]: restrict an actual
    isotropy operator to the transverse block, supporting I
    isomorphic and isometric with O(n-1), 3.2.47,
    pp. 282–283. *)
Definition spherical_coordinate_restriction (R:realType) n
    (H:Hom (R_n R (1+n)) (R_n R (1+n))):Hom (R_n R n) (R_n R n):=
  hom_comp (@euclidean_last_block_map R 1 n)
    (hom_comp H (@euclidean_last_injection_map R 1 n)).

(** Source for [spherical_coordinate_first_injection]: the whole
    first block is the scalar span of the actual pole,
    supporting the isotropy identification of 3.2.47, p. 282. *)
Lemma spherical_coordinate_first_injection (R:realType) n (u:R_n R 1):
  @euclidean_first_injection R 1 n u=u ord0*:spherical_coordinate_pole R n.
Proof.
have hOne:u=u ord0*:@coordinate_basis R 1 ord0.
  apply/ffunP=>i; rewrite (ord1 i) /coordinate_basis !ffunE eqxx.
  change (u ord0=u ord0*1); exact:esym (mulr1 (u ord0)).
rewrite {1}hOne (linZ (@euclidean_first_injection_linear R 1 n)).
congr (_ *: _); exact (esym (@euclidean_block_basis_left R 1 n ord0)).
Qed.

(** Source for [spherical_coordinate_isotropy_transverse]: an actual
    orthogonal operator fixing the pole preserves its perpendicular
    transverse block, supporting 3.2.47, pp. 282–283. *)
Lemma spherical_coordinate_isotropy_transverse (R:realType) n
    (H:Hom (R_n R (1+n)) (R_n R (1+n))):
  spherical_orthogonal_isotropy (spherical_coordinate_pole R n) H ->forall y,
  H (@euclidean_last_injection R 1 n y)=
    @euclidean_last_injection R 1 n (spherical_coordinate_restriction H y).
Proof.
move=>[hOrthogonal hFixed] y.
have hPair:euclidean_inner_product (H (@euclidean_last_injection R 1 n y))
    (spherical_coordinate_pole R n)=0.
  rewrite -hFixed hOrthogonal /spherical_coordinate_pole euclidean_inner_basis
    /euclidean_last_injection euclidean_block_join_left ffunE; reflexivity.
rewrite /spherical_coordinate_pole euclidean_inner_basis in hPair.
have hFirst:@euclidean_first_block R 1 n (H (@euclidean_last_injection R 1 n y))=0.
  apply/ffunP=>i; rewrite /euclidean_first_block !ffunE (ord1 i).
  exact hPair.
apply:euclidean_block_vectors_ext.
- move=>i.
  have hZero:=congr1 (fun v:R_n R 1=>v i) hFirst.
  rewrite /euclidean_first_block !ffunE in hZero.
  rewrite /euclidean_last_injection euclidean_block_join_left ffunE; exact hZero.
- move=>i; rewrite /euclidean_last_injection euclidean_block_join_right.
  change (H (@euclidean_last_injection R 1 n y) (rshift 1 i)=
    @euclidean_last_block R 1 n (H (@euclidean_last_injection R 1 n y)) i).
  by rewrite /euclidean_last_block ffunE.
Qed.

(** Source for [spherical_coordinate_isotropy_restriction_orthogonal]: the
    actual transverse restriction belongs to O(n-1), supporting
    the isotropy assertion in 3.2.47, p. 282. *)
Theorem spherical_coordinate_isotropy_restriction_orthogonal (R:realType) n
    (H:Hom (R_n R (1+n)) (R_n R (1+n))):
  spherical_orthogonal_isotropy (spherical_coordinate_pole R n) H ->
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n)
    (hom_as_linear (spherical_coordinate_restriction H)).
Proof.
move=>hIsotropy y z.
have hInjection v w:euclidean_inner_product (@euclidean_last_injection R 1 n v)
    (@euclidean_last_injection R 1 n w)=euclidean_inner_product v w.
  rewrite /euclidean_last_injection euclidean_block_join_inner /=.
  by rewrite (bil0l (inner_bilinear (@euclidean_inner_productP R 1))) add0r.
have hPair:=hIsotropy.1 (@euclidean_last_injection R 1 n y) (@euclidean_last_injection R 1 n z).
change (euclidean_inner_product
  (H (@euclidean_last_injection R 1 n y)) (H (@euclidean_last_injection R 1 n z))=
  euclidean_inner_product (@euclidean_last_injection R 1 n y)
    (@euclidean_last_injection R 1 n z)) in hPair.
rewrite !(spherical_coordinate_isotropy_transverse hIsotropy) !hInjection in hPair.
exact hPair.
Qed.

(** Source for [spherical_coordinate_isotropy_extension_law]: every
    original isotropy operator is exactly its transverse restriction
    extended by the identity on the pole line; supporting
    3.2.47, p. 282. *)
Theorem spherical_coordinate_isotropy_extension_law (R:realType) n
    (H:Hom (R_n R (1+n)) (R_n R (1+n))):
  spherical_orthogonal_isotropy (spherical_coordinate_pole R n) H ->
  is_euclidean_block_extension (hom_as_linear (spherical_coordinate_restriction H)) (hom_as_linear H).
Proof.
move=>hIsotropy u y.
have hFirst:H (@euclidean_first_injection R 1 n u)=@euclidean_first_injection R 1 n u.
  rewrite !spherical_coordinate_first_injection.
  exact (eq_trans (linZ (hom_linear H) (u ord0) (spherical_coordinate_pole R n))
    (congr1 (fun z=>u ord0*:z) hIsotropy.2)).
change (H (euclidean_block_join (u,y))=
  euclidean_block_join (u,spherical_coordinate_restriction H y)).
rewrite !euclidean_block_join_decomposition.
exact (eq_trans (linD (hom_linear H) (@euclidean_first_injection R 1 n u)
  (@euclidean_last_injection R 1 n y))
  (congr2 (fun x z:R_n R (1+n)=>x+z) hFirst
    (@spherical_coordinate_isotropy_transverse R n H hIsotropy y))).
Qed.

(** Source for [spherical_coordinate_isotropy_reconstruction]: extension
    after restriction recovers every actual member of I,
    supporting the exact isomorphism of 3.2.47, p. 282. *)
Theorem spherical_coordinate_isotropy_reconstruction (R:realType) n
    (H:Hom (R_n R (1+n)) (R_n R (1+n))):
  spherical_orthogonal_isotropy (spherical_coordinate_pole R n) H ->
  hom_of_linear (@euclidean_block_extension R 1 n
    (hom_as_linear (spherical_coordinate_restriction H)))=H.
Proof.
move=>hIsotropy; apply:hom_ext=>x.
exact (@euclidean_block_extension_unique R 1 n
  (hom_as_linear (spherical_coordinate_restriction H))
  (@euclidean_block_extension R 1 n (hom_as_linear (spherical_coordinate_restriction H)))
  (hom_as_linear H) (@euclidean_block_extension_specification R 1 n
    (hom_as_linear (spherical_coordinate_restriction H)))
  (spherical_coordinate_isotropy_extension_law hIsotropy) x).
Qed.

(** Source for [spherical_coordinate_extension_member]: every actual
    O(n-1) operator extends to the original isotropy I,
    including n-1=0, 3.2.47, p. 282. *)
Theorem spherical_coordinate_extension_member (R:realType) n
    (h:Hom (R_n R n) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) (hom_as_linear h) ->
  spherical_orthogonal_isotropy (spherical_coordinate_pole R n)
    (hom_of_linear (@euclidean_block_extension R 1 n (hom_as_linear h))).
Proof.
move=>hOrthogonal; split.
- exact (@euclidean_block_extension_orthogonal R 1 n (hom_as_linear h) hOrthogonal).
-
rewrite /spherical_coordinate_pole euclidean_block_basis_left hom_of_linearE
  euclidean_block_extension_specification linear0; reflexivity.
Qed.

(** Source for [spherical_coordinate_restriction_extension]: restriction
    after extension is the original O(n-1) operator,
    supporting the exact isotropy isomorphism of 3.2.47, p. 282. *)
Theorem spherical_coordinate_restriction_extension (R:realType) n
    (h:Hom (R_n R n) (R_n R n)):
  spherical_coordinate_restriction
    (hom_of_linear (@euclidean_block_extension R 1 n (hom_as_linear h)))=h.
Proof.
apply:hom_ext=>y.
change (@euclidean_last_block R 1 n
  (@euclidean_block_extension R 1 n (hom_as_linear h) (@euclidean_last_injection R 1 n y))=h y).
rewrite /euclidean_last_injection euclidean_block_extension_specification.
exact (congr1 snd (@euclidean_block_joinK R 1 n ((0:R_n R 1),h y))).
Qed.

(** Source for [spherical_coordinate_isotropy_distance]: the preceding
    exact parametrization preserves the actual Hilbert Hom distances,
    as required for I isometric with O(n-1) in
    3.2.47, pp. 282–283. *)
Theorem spherical_coordinate_isotropy_distance (R:realType) n
    (h g:Hom (R_n R n) (R_n R n)):
  inner_norm (@euclidean_hom_inner_productP R (1+n) (1+n))
    (hom_of_linear (@euclidean_block_extension R 1 n (hom_as_linear h))-
     hom_of_linear (@euclidean_block_extension R 1 n (hom_as_linear g)))=
  inner_norm (@euclidean_hom_inner_productP R n n) (h-g).
Proof. exact:euclidean_block_extension_difference_norm. Qed.
