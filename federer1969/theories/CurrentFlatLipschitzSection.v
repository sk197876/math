(** Federer (1969), 4.1.15, p. 373: if g composed with
    f is identity, flat currents supported in the image of f,
    currents fixed by f# composed with g#, and currents in the
    image of f# form the same set. Only the preceding support
    coincidence and the formal properties of 4.1.14 are used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP CurrentSpaces CurrentSupportGeometry FlatCurrentsUP
  NormRegularity NormRegularityOperations
  CurrentOpenIdentitySmooth NormLocalLipschitzScalarProduct
  MetricLocalLipschitzComposition CurrentFlatLipschitzPushforwardSealed
  CurrentFlatLipschitzPushforwardBasic CurrentFlatLipschitzComposition
  CurrentFlatLipschitzProofIndependence CurrentFlatLipschitzSupportAgreement
  CurrentFlatIdentityPushforward CurrentAboveDimension FlatCurrentUnion
  CurrentFlatPushforwardZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentFlatLipschitzSection.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n nu m : nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U : set X) (V : set Y).
Hypothesis hU : forall x,U x->norm_domain_interior NX U x.
Hypothesis hV : forall y,V y->norm_domain_interior NY V y.
Variables (f : X->Y) (g : Y->X).
Hypothesis hFImage : forall x,U x->V (f x).
Hypothesis hGImage : forall y,V y->U (g y).
Hypothesis hFLocal : @is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Hypothesis hGLocal : @is_locally_metric_lipschitz R
  (real_norm_metric_space hNY) (real_norm_metric_space hNX) V g.
Hypothesis hLeftInverse : forall x,U x->g (f x)=x.
Local Notation CX := (@current_space R h2 n U hU m).
Local Notation CY := (@current_space R h2 nu V hV m).
Local Notation FlatX := (@is_flat_current R h2 n m U hU).
Local Notation FlatY := (@is_flat_current R h2 nu m V hV).
Local Notation F := (@CurrentFlatLipschitzPushforward.value R h2 n nu m
  U V hU hV f hFImage hFLocal).
Local Notation G := (@CurrentFlatLipschitzPushforward.value R h2 nu n m
  V U hV hU g hGImage hGLocal).
Local Notation FG := (fun y=>f (g y)).
Let hFGImage : forall y,V y->V (FG y) :=
  fun y hy=>@hFImage (g y) (@hGImage y hy).
Let hFGLocal := @metric_local_lipschitz_composition R
  (real_norm_metric_space hNY) (real_norm_metric_space hNX)
  (real_norm_metric_space hNY) V U g f hGImage hGLocal hFLocal.
Let hIdImage : forall y,V y->V y := fun y hy=>hy.
Let hIdLocal : @is_locally_metric_lipschitz R
    (real_norm_metric_space hNY) (real_norm_metric_space hNY) V
    (fun y=>y).
Proof.
apply:(@norm_class_one_locally_metric_lipschitz R Y Y NY NY hNY hNY V
  (fun y=>y)).
apply:((@norm_class_firstP R Y Y NY NY hNY hNY V (fun y=>y)).1).
exact:(@current_open_identity_smooth R nu V hV 1).
Qed.

(** Source for [current_flat_lipschitz_section_supported_fixed]:
    every flat current supported in im f is fixed by f# g#,
    Federer 4.1.15, p. 373, displayed set equality. *)
Theorem current_flat_lipschitz_section_supported_fixed
    (S : CY) (hS : FlatY S) :
  @current_support R h2 nu V hV m S `<=` f @` U ->
  S=F (G S hS)
    (proj1 (@CurrentFlatLipschitzPushforward.laws R h2 nu n m V U hV hU
      g hGImage hGLocal S hS)).
Proof.
move=>hSupport.
have hAgreement : forall y,@current_support R h2 nu V hV m S y->FG y=y.
  move=>y hy; have [x hx <-]:=@hSupport y hy.
  by rewrite /FG (@hLeftInverse x hx).
have hSame:=@current_flat_lipschitz_support_agreement R h2 nu nu m V V hV hV
  FG (fun y=>y) hFGImage hIdImage hFGLocal hIdLocal S hS hAgreement.
have hIdentity:=@current_flat_lipschitz_identity_pushforward R h2 nu m V hV
  hIdImage hIdLocal S hS.
have hComposition:=@current_flat_lipschitz_pushforward_composition R h2
  nu n nu m V U V hV hU hV g f hGImage hFImage hGLocal hFLocal S hS.
apply:(eq_trans (esym hIdentity)).
apply:(eq_trans (esym hSame)).
exact:hComposition.
Qed.

(** Source for [current_flat_lipschitz_section_fixed_image]:
    a fixed current is the image of the flat current g#S,
    the middle-to-last inclusion of the set equality in
    Federer 4.1.15, p. 373. *)
Theorem current_flat_lipschitz_section_fixed_image
    (S : CY) (hS : FlatY S) :
  S=F (G S hS)
    (proj1 (@CurrentFlatLipschitzPushforward.laws R h2 nu n m V U hV hU
      g hGImage hGLocal S hS)) ->
  exists (T : CX) (hT : FlatX T),F T hT=S.
Proof.
move=>hFixed.
exists (G S hS),
  (proj1 (@CurrentFlatLipschitzPushforward.laws R h2 nu n m V U hV hU
    g hGImage hGLocal S hS)).
exact:esym hFixed.
Qed.

(** Source for [current_flat_lipschitz_section_image_supported]:
    every image under f# is supported in im f, the final-to-first
    inclusion of Federer 4.1.15, p. 373. The existing sharp image
    support law gives the assertion for arbitrary flat inputs. *)
Theorem current_flat_lipschitz_section_image_supported
    (S : CY) :
  (exists (T : CX) (hT : FlatX T),F T hT=S) ->
  @current_support R h2 nu V hV m S `<=` f @` U.
Proof.
move=>[T [hT <-]] y hy.
have [x hx <-]:=@current_flat_lipschitz_pushforward_support R h2 n nu m
  U V hU hV f hFImage hFLocal T hT y hy.
exists x; first exact:hx.1.
by [].
Qed.

(** Source for [current_flat_lipschitz_section]: all three
    sets in the original display are equal, Federer 4.1.15,
    p. 373. The two equivalences retain the same actual current
    and arbitrary evidence of its original flat membership. *)
Theorem current_flat_lipschitz_section (S : CY) (hS : FlatY S) :
  ((@current_support R h2 nu V hV m S `<=` f @` U) <->
    S=F (G S hS)
      (proj1 (@CurrentFlatLipschitzPushforward.laws R h2 nu n m V U hV hU
        g hGImage hGLocal S hS))) /\
  ((@current_support R h2 nu V hV m S `<=` f @` U) <->
    exists (T : CX) (hT : FlatX T),F T hT=S).
Proof.
split; split.
- exact:current_flat_lipschitz_section_supported_fixed.
- move=>hFixed; exact:(@current_flat_lipschitz_section_image_supported S
    (@current_flat_lipschitz_section_fixed_image S hS hFixed)).
- move=>hSupport; exact:(@current_flat_lipschitz_section_fixed_image S hS
    (@current_flat_lipschitz_section_supported_fixed S hS hSupport)).
- exact:current_flat_lipschitz_section_image_supported.
Qed.

(** Source for [current_flat_lipschitz_section_above_dimension]:
    the image-set equality and D_m(R^(m-1))=0 give
    the affine-subspace support corollary in Federer 4.1.15,
    p. 373. This supporting form allows every lower-dimensional
    Lipschitz section, with no finite mass or normality premise. *)
Theorem current_flat_lipschitz_section_above_dimension
    (hDegree : (n<m)%N) (S : CY) (hS : FlatY S)
    (hSupport : @current_support R h2 nu V hV m S `<=` f @` U) :
  S=0.
Proof.
have hFixed:=@current_flat_lipschitz_section_supported_fixed S hS hSupport.
have [T [hT hImage]]:=@current_flat_lipschitz_section_fixed_image S hS hFixed.
have hTZero:=@current_above_dimension R h2 n m hDegree U hU T.
pose hZero:=@flat_current_zero R h2 n m U hU.
have hCongruence:=@current_flat_lipschitz_pushforward_congruence R h2 n nu m
  U V hU hV f hFImage hFLocal T 0 hT hZero hTZero.
have hZeroImage:=@current_flat_lipschitz_pushforward_zero R h2 n nu m
  U V hU hV f hFImage hFLocal hZero.
exact:(eq_trans (esym hImage) (eq_trans hCongruence hZeroImage)).
Qed.
End CurrentFlatLipschitzSection.

Arguments current_flat_lipschitz_section_supported_fixed : clear implicits.
Arguments current_flat_lipschitz_section_fixed_image : clear implicits.
Arguments current_flat_lipschitz_section_image_supported : clear implicits.
Arguments current_flat_lipschitz_section : clear implicits.
Arguments current_flat_lipschitz_section_above_dimension : clear implicits.
