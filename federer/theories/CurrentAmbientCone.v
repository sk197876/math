(** Federer (1969), 4.1.10, p. 364: the original cone
    h#([0,1] times T) of a compactly supported current, first in
    the whole ambient R^n. This is a specialization of the existing
    opaque deformation chain, not a new current construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentHomotopyUP CurrentHomotopyCylinder CurrentHomotopyCompactCylinder
  CurrentDeformationChainSealed CurrentDeformationChainCompact
  CurrentConeHomotopySealed CurrentConeHomotopyClass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentAmbientCone.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n j : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hOpen : forall x, U x -> norm_domain_interior NX U x.
Variable u : X.
Local Notation V := (fun _:X => True).
Local Notation A := (fun _:R => True).
Local Notation f := (fun _:X => u).
Local Notation g := (fun x:X => x).
Local Notation h := (@CurrentConeHomotopy.value R n u).
Local Notation hH := (@current_cone_ambient_homotopy R n u U hOpen).
Local Notation hU := (@current_homotopy_source_open R n n A U V f g h hH.1).
Local Notation hV := (@current_homotopy_target_open R n n A U V f g h hH.1).
Variable T : @current_space R h2 n U hU j.
Hypothesis hCompact : @compact (real_norm_metric_space hNX) (@current_support R h2 n U hU j T).
Local Notation hProper := (@current_homotopy_compact_support_proper R h2 n n j
  A U V f g h hH T hCompact).

(** Source for [current_ambient_cone]: the original affine
    deformation chain in Federer 4.1.10, p. 364. The existing
    opaque chain receives only the derived support-cylinder properness. *)
Definition current_ambient_cone : @current_space R h2 n V hV (1+j)%N :=
  @CurrentDeformationChain.value R h2 n n j A U V f g h hH T hProper.

(** Source for [current_ambient_cone_compact]: the original
    cone has compact support when T does, supporting Federer
    4.1.10, p. 364. The previous compact product and pushforward
    theorems apply without a representation or finite-mass premise. *)
Theorem current_ambient_cone_compact :
  @compact (real_norm_metric_space hNX)
    (@current_support R h2 n V hV (1+j)%N current_ambient_cone).
Proof.
exact: (@current_deformation_chain_compact R h2 n n j A U V f g h hH T hCompact hProper).
Qed.
End CurrentAmbientCone.
