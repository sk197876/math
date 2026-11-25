(** Federer (1969), 4.1.10, p. 364: the original cone
    restricted to the original open U. Its independent specification
    is its action on every actual test form. The existing ambient
    cone and test zero extension specify that action; continuity and
    existence are proved separately. Star-shapedness will ensure the
    original compact segment support is contained in U. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentEvaluation CurrentOpenRestriction CurrentHomotopyUP CurrentHomotopyGeometry
  CurrentConeHomotopySealed CurrentConeHomotopyClass CurrentAmbientCone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentOpenConeUP.
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
Local Notation hUV := (@current_homotopy_endpoint_images R n n A U V f g h hH.1).2.
Variable T : @current_space R h2 n U hU j.
Hypothesis hCompact : @compact (real_norm_metric_space hNX) (@current_support R h2 n U hU j T).
Local Notation ambient := (@current_ambient_cone R h2 n j U hOpen u T hCompact).
Local Notation extension := (@current_open_test_extension R h2 n (1+j)%N U V hU hV hUV).

(** Source for [is_current_open_cone]: the original cone's
    action on U is its ambient action on zero-extended compact tests,
    supporting the arbitrary star-shaped extension in Federer 4.1.10,
    p. 364. No witness or continuity assertion occurs in this law. *)
Definition is_current_open_cone (S : @current_space R h2 n U hU (1+j)%N) : Prop :=
  forall psi, @current_value R h2 n U hU (1+j)%N S psi=
    @current_value R h2 n V hV (1+j)%N ambient (extension psi).

(** Source for [current_open_cone_exists]: original current
    restriction supplies a continuous current with the specified
    cone action, supporting Federer 4.1.10, p. 364. The construction
    serves only as this existence proof. *)
Theorem current_open_cone_exists :
  exists S : @current_space R h2 n U hU (1+j)%N, is_current_open_cone S.
Proof.
exists (@current_open_restriction R h2 n (1+j)%N U V hU hV hUV ambient).
move=> psi; exact: current_open_restriction_evaluation.
Qed.

(** Source for [current_open_cone_unique]: the original test
    action determines the cone uniquely, supporting Federer 4.1.10,
    p. 364, without exposing the restriction construction. *)
Theorem current_open_cone_unique (S Q : @current_space R h2 n U hU (1+j)%N) :
  is_current_open_cone S -> is_current_open_cone Q -> S=Q.
Proof.
move=> hS hQ; apply: current_values_extensional => psi.
exact: eq_trans (hS psi) (esym (hQ psi)).
Qed.
End CurrentOpenConeUP.
