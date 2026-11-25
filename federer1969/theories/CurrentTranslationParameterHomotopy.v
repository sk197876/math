(** Federer (1969), 4.1.18, p. 374: the
    original fixed-z translation homotopies are the fibres
    of the actual smooth map (t,z,x) maps to
    x+t z. Reuse the earlier opaque affine homotopy;
    keep the z and x blocks distinct.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology ring.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormFiniteLinearBound NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates
  EuclideanBlockLinearMaps EuclideanCartesianMap CurrentCartesianDomain
  CurrentAffineHomotopyUP CurrentAffineHomotopySealed CurrentAffineHomotopyClass
  CurrentAffineHomotopyGeometry CurrentHomotopyUP CurrentHomotopyDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentTranslationParameterHomotopy.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation Z:=(R_n R (n+n)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R (n+n))).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R (n+n))).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:Z=>True).
Local Notation hFull:=(fun (x:Z) (_:True)=>norm_full_domain_interior NZ x).
Local Notation p:=(@euclidean_first_block_map R n n).
Local Notation q:=(@euclidean_last_block_map R n n).

(** Source for [current_translation_parameter_end]: the
    endpoint (z,x) maps to x+z in the
    averaging display of Federer 4.1.18, p. 374. *)
Definition current_translation_parameter_end:Hom Z X:=q+p.
Local Notation End:=current_translation_parameter_end.

(** Source for [current_translation_parameter_start_smooth]:
    the original starting projection is smooth,
    supporting Federer 4.1.18, p. 374. *)
Lemma current_translation_parameter_start_smooth:
  norm_class_all_orders hNZ hNX Full q.
Proof.
move=>k;apply:(@norm_class_linear R Z X NZ NX hNZ hNX Full q k hFull).
exact:(@norm_finite_linear_bounded R Z X NZ NX hNZ hNX (n+n)%N
  (@coordinate_basis R (n+n)) (@coordinate_basisP R (n+n)) q).
Qed.

(** Source for [current_translation_parameter_end_smooth]:
    the original endpoint addition is smooth,
    supporting Federer 4.1.18, p. 374. *)
Lemma current_translation_parameter_end_smooth:
  norm_class_all_orders hNZ hNX Full End.
Proof.
move=>k;apply:(@norm_class_linear R Z X NZ NX hNZ hNX Full End k hFull).
exact:(@norm_finite_linear_bounded R Z X NZ NX hNZ hNX (n+n)%N
  (@coordinate_basis R (n+n)) (@coordinate_basisP R (n+n)) End).
Qed.

(** Source for [current_translation_parameter_homotopy]:
    the existing affine homotopy with endpoints x and
    x+z, supporting Federer 4.1.18, p. 374. *)
Definition current_translation_parameter_homotopy:=
  @CurrentAffineHomotopy.value R (n+n)%N n q End.
Local Notation H:=current_translation_parameter_homotopy.

(** Source for [current_translation_parameter_homotopy_laws]:
    actual original smooth homotopy data for every real
    time and every (z,x), supporting 4.1.18, p. 374. *)
Definition current_translation_parameter_homotopy_laws:
  @is_smooth_current_homotopy R (n+n)%N n (fun _=>True) Full
    (fun _=>True) q End H:=
  @current_affine_ambient_homotopy R (n+n)%N n Full hFull q End
    current_translation_parameter_start_smooth current_translation_parameter_end_smooth.

(** Source for [current_translation_parameter_homotopy_coordinates]:
    the literal formula h_z(t,x)=x+t z from
    Federer 4.1.18, p. 374. This identity does
    not bound the whole (z,x) differential by one. *)
Theorem current_translation_parameter_homotopy_coordinates y:
  H y=q (@euclidean_last_block_map R 1%N (n+n)%N y)+
    (@euclidean_one_project R (@euclidean_first_block_map R 1%N (n+n)%N y))*:
      p (@euclidean_last_block_map R 1%N (n+n)%N y).
Proof.
rewrite /current_translation_parameter_homotopy
  current_affine_homotopy_coordinates /current_translation_parameter_end
  hom_addE scalerDr scalerBl scale1r.
apply/ffunP=>i;rewrite !ffunE;ring.
Qed.

(** Source for [current_translation_parameter_homotopy_smooth_whole]:
    the same literal map is smooth on the whole
    ambient parameter space, supporting the compact-locus
    properness proof for 4.1.18, p. 374. *)
Theorem current_translation_parameter_homotopy_smooth_whole:
  norm_class_all_orders
    (inner_norm_real_norm (@euclidean_inner_productP R (1+(n+n))%N)) hNX
    (fun _=>True) H.
Proof.
have hDomain:@current_homotopy_product_domain R (n+n)%N (fun _=>True) Full=
    (fun _=>True).
  apply:funext=>y;apply:propext;split;first by move=>_.
  by move=>_;split.
by rewrite -hDomain;exact:current_translation_parameter_homotopy_laws.2.
Qed.
End CurrentTranslationParameterHomotopy.
