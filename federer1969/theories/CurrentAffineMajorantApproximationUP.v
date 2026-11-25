(** Federer (1969), 4.1.14, pp. 371–372: independently
    specify compatible smooth affine approximants with the
    original continuous derivative majorant. One open time-space
    source maps entirely into the original arbitrary open V.
    Existence is separate and assumes segments only over K. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentLipschitzCompactImage CurrentHomotopyUP
  CurrentAffineHomotopySealed CurrentCompactTimeCylinder CurrentSmoothApproximationUP
  CurrentMapDifferential EuclideanHomOperator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentAffineMajorantApproximationUP.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).

(** Source for [is_current_affine_majorant_approximation]:
    the actual compatible affine smoothing used in Federer
    4.1.14, pp. 371–372. The endpoint caps retain the
    original sigma on K; the homotopy family meets the
    preceding original universal approximation specification. *)
Record is_current_affine_majorant_approximation
    (U:set X) (V:set Y) (K:smooth_compact_set hNX U)
    (f g:X->Y) (sigma:X->R^o)
    (A:set R) (W:set X) (a b:nat->X->Y) (eta:nat->R):Prop:={
  (** Source: original open time interval, 4.1.9, p. 363. *)
  current_affine_majorant_parameter:@is_homotopy_parameter_interval R A;
  (** Source: one source neighbourhood of K, 4.1.14, pp. 370–371. *)
  current_affine_majorant_domain_open:forall x,W x->norm_domain_interior NX W x;
  (** Source: the original compact support stays in the source, p. 371. *)
  current_affine_majorant_domain_contains:smooth_compact_carrier K `<=` W;
  (** Source: shrinking the original open U, 4.1.13, pp. 369–370. *)
  current_affine_majorant_domain_in_domain:W `<=` U;
  (** Source: the empty compact case in the same approximation. *)
  current_affine_majorant_empty_domain:smooth_compact_carrier K=set0->W=set0;
  (** Source: the original affine map has its image in V on the
      internally derived open source, 4.1.14, pp. 371–372. *)
  current_affine_majorant_original_image:forall z,
    @current_homotopy_product_domain R n A W z->
      V (@CurrentAffineHomotopy.value R n nu f g z);
  (** Source: actual smooth first endpoints, 4.1.14, pp. 370–371. *)
  current_affine_majorant_first_approximation:
    @is_current_smooth_approximation R n nu W V
      (@current_compact_index_in_open R n U W K current_affine_majorant_domain_contains)
      f a;
  (** Source: actual smooth second endpoints, 4.1.14, pp. 370–371. *)
  current_affine_majorant_second_approximation:
    @is_current_smooth_approximation R n nu W V
      (@current_compact_index_in_open R n U W K current_affine_majorant_domain_contains)
      g b;
  (** Source: positive vanishing derivative error, 4.1.14, p. 371. *)
  current_affine_majorant_error_positive:forall i,0<eta i;
  (** Source: remove the smoothing error in the original bound, p. 371. *)
  current_affine_majorant_error_zero:forall eps:R,0<eps->exists N:nat,
    forall i:nat,(N<=i)%N->eta i<eps;
  (** Source: the actual endpoint differential cap only on K, p. 371. *)
  current_affine_majorant_first_cap:forall i x,smooth_compact_carrier K x->
    @euclidean_operator_norm R n nu (@current_map_differential R n nu W (a i) x)
      <=sigma x+eta i;
  (** Source: the same original majorant for the other endpoint, p. 371. *)
  current_affine_majorant_second_cap:forall i x,smooth_compact_carrier K x->
    @euclidean_operator_norm R n nu (@current_map_differential R n nu W (b i) x)
      <=sigma x+eta i;
  (** Source: the actual affine H_i is an original allowed smooth
      approximation of H on the closed time cylinder, pp. 371–372. *)
  current_affine_majorant_homotopy_approximation:
    @is_current_smooth_approximation R (1+n)%N nu
      (@current_homotopy_product_domain R n A W) V
      (@current_compact_time_cylinder R n A W current_affine_majorant_parameter
        (@current_compact_index_in_open R n U W K current_affine_majorant_domain_contains))
      (@CurrentAffineHomotopy.value R n nu f g)
      (fun i=>@CurrentAffineHomotopy.value R n nu (a i) (b i))
}.
End CurrentAffineMajorantApproximationUP.
