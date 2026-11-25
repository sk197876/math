(** Federer (1969), 4.1.18, p. 374: the
    original h_z(t,x)=x+t z is the existing
    opaque affine homotopy from identity to translation.
    Its actual geometry, values and fibre displacement
    are proved from the old laws.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology ring.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity NormClassZeroTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockLinearMaps
  CurrentJoinSliceMapClass CurrentTranslations EuclideanAdditiveGroup
  CurrentHomotopyUP CurrentHomotopyDomain CurrentCompactTimeCylinder
  CurrentAffineHomotopySealed CurrentAffineHomotopyClass CurrentAffineHomotopyGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentTranslationHomotopy.
Variable R:realType.
Variable n:nat.
Variable z:R_n R n.
Local Notation X:=(R_n R n).
Local Notation P:=(R_n R (1+n)%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NP:=(inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNP:=(inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation Id:=(fun x:X=>x).
Local Notation tau:=(@euclidean_translation R n z).

(** Source for [current_translation_homotopy]: the original
    h_z of 4.1.18, p. 374, is the old
    affine operator from 4.1.9 and 4.1.13. *)
Definition current_translation_homotopy:=@CurrentAffineHomotopy.value R n n Id tau.
Local Notation H:=current_translation_homotopy.

(** Source for [current_translation_homotopy_laws]: original
    smooth homotopy data on the whole time-space
    source, supporting 4.1.18, p. 374. *)
Definition current_translation_homotopy_laws:
  @is_smooth_current_homotopy R n n (fun _=>True) Full Full Id tau H:=
  @current_affine_ambient_homotopy R n n Full hFull Id tau
    (@current_join_slice_identity_smooth R n) (@current_translation_smooth R n z).

(** Source for [current_translation_homotopy_coordinates]: the
    literal h_z(t,x)=x+t z in 4.1.18, p. 374. *)
Theorem current_translation_homotopy_coordinates y:
  H y=@euclidean_last_block_map R 1%N n y+
    (@euclidean_one_project R (@euclidean_first_block_map R 1%N n y))*:z.
Proof.
rewrite /current_translation_homotopy current_affine_homotopy_coordinates
  /euclidean_translation scalerDr scalerBl scale1r.
apply/ffunP=>i;rewrite !ffunE;ring.
Qed.

(** Source for [current_translation_homotopy_smooth_whole]: the
    same actual homotopy is smooth in the whole
    ambient time-space presentation, supporting properness
    of the literal cylinder in 4.1.18, p. 374. *)
Theorem current_translation_homotopy_smooth_whole:
  norm_class_all_orders hNP hNX (fun _=>True) H.
Proof.
have hDomain:@current_homotopy_product_domain R n (fun _=>True) Full=(fun _=>True).
  apply:funext=>y;apply:propext;split;first by move=>_.
  by move=>_;split.
by rewrite -hDomain;exact:current_translation_homotopy_laws.2.
Qed.

(** Source for [current_translation_homotopy_displacement]:
    each original h_z moves spatial points by at
    most |z| on [0,1], supporting properness and
    sharp deformation mass in 4.1.18, p. 374. *)
Theorem current_translation_homotopy_displacement y:
  0<=@euclidean_one_project R (@euclidean_first_block_map R 1%N n y)<=1 ->
  NX (H y-@euclidean_last_block_map R 1%N n y)<=NX z.
Proof.
move=>ht.
rewrite current_translation_homotopy_coordinates addrAC subrr add0r inner_normZ.
have hTime:`|@euclidean_one_project R (@euclidean_first_block_map R 1%N n y)|<=1.
  rewrite (ger0_norm (andP ht).1);exact:(andP ht).2.
have h:=ler_wpM2r (inner_norm_nonnegative (@euclidean_inner_productP R n) z) hTime.
by rewrite mul1r in h.
Qed.
End CurrentTranslationHomotopy.
