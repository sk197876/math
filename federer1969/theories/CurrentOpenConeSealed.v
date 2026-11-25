(** Federer (1969), 4.1.10, p. 364: the original cone in
    the original open domain. Its actual test action is specified
    independently, existence and uniqueness are proved, and the chosen
    restriction witness remains hidden behind this interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentHomotopyUP CurrentConeHomotopySealed CurrentConeHomotopyClass
  CurrentOpenConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentOpenConeSignature.
Section Operators.
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
Local Notation C := (@current_space R h2 n U hU j).
Local Notation compact_support T := (@compact (real_norm_metric_space hNX)
  (@current_support R h2 n U hU j T)).
Local Notation S := (@current_space R h2 n U hU (1+j)%N).
(** Source for [value]: the original cone current on U,
    supporting Federer 4.1.10, p. 364, final mathematical paragraph. *)
Parameter value : forall (T:C), compact_support T -> S.
(** Source for [laws]: every original test has exactly its
    specified cone action, supporting Federer 4.1.10, p. 364. *)
Parameter laws : forall (T:C) (hCompact:compact_support T),
  @is_current_open_cone R h2 n j U hOpen u T hCompact (@value T hCompact).
End Operators.
End CurrentOpenConeSignature.
Module CurrentOpenCone : CurrentOpenConeSignature.
Section Operators.
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
Local Notation C := (@current_space R h2 n U hU j).
Local Notation compact_support T := (@compact (real_norm_metric_space hNX)
  (@current_support R h2 n U hU j T)).
Local Notation S := (@current_space R h2 n U hU (1+j)%N).
(** Source for [value]: hide the proved existence witness
    for the original cone action, supporting Federer 4.1.10, p. 364. *)
Definition value (T:C) (hCompact:compact_support T) : S :=
  projT1 (cid (@current_open_cone_exists R h2 n j U hOpen u T hCompact)).
(** Source for [laws]: the sealed cone has the independent
    original action, supporting Federer 4.1.10, p. 364. *)
Lemma laws (T:C) (hCompact:compact_support T) :
  @is_current_open_cone R h2 n j U hOpen u T hCompact (@value T hCompact).
Proof.
exact: (projT2 (cid (@current_open_cone_exists R h2 n j U hOpen u T hCompact))).
Qed.
End Operators.
End CurrentOpenCone.
