(** Federer (1969), 4.1.7, p. 359:
    the original half-line example requires
    properness on the current's support.
    This account collects its literal point
    pushforward and the failure of the
    support conclusion for the displayed primitive.
    The separate uniqueness correction retains agreement
    with the original T on U. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate CurrentSpaces CurrentBoundary
  CurrentDirac CurrentDiracDensity DiracCurrentBounds CurrentSupportGeometry CurrentProperSupport
  CurrentPushforwardSealed CurrentPushforwardCongruence CurrentPushforwardDirac HalflineCurrents HalflineCurrentBoundary
  HalflinePrimitiveBoundary HalflineCurrentSupport HalflineCurrentSupportObstruction
  HalflineFiniteNormalMass HalflineCurrentTopology HalflineInclusionSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HalflineCurrentExample.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1)).
Local Notation U := (@current_halfline_domain R).
Local Notation hU := (@current_halfline_domain_open R).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation hImage := (fun (x:X) (_:U x)=>Logic.I).
Local Notation T := (@halfline_current R h2).
Local Notation S := (@halfline_left_primitive_candidate R h2).
Local Notation supportU := (@current_support R h2 1 U hU 1%N).
Local Notation supportR := (@current_support R h2 1 Full hFull 1%N).
Variable b:R.
Hypothesis hb:0<b.

(** Source for [halfline_boundary_support_proper]:
    the original inclusion is proper on
    the singleton support of boundary T,
    Federer 4.1.7, p. 359. This
    does not make it proper on
    the whole support of T. *)
Theorem halfline_boundary_support_proper:
  @is_current_proper_on_support R h2 1 1 0%N U hU Full
    (@current_boundary R h2 1 0%N U hU (T b)) id hImage.
Proof.
rewrite halfline_current_boundary.
apply:(@current_point_support_proper R h2 1 1 U Full hU
  (euclidean_one_embed b) _ id hImage).
by change (is_true (0<euclidean_one_project (euclidean_one_embed b)));
  rewrite euclidean_one_embedK;exact:hb.
Qed.

(** Source for [halfline_boundary_pushforward]: the
    original identity f#(boundary T)=delta_b
    holds for the actual inclusion, Federer
    4.1.7, p. 359. The whole
    current T lacks the properness needed
    to apply the boundary theorem to it. *)
Theorem halfline_boundary_pushforward:
  @CurrentPushforward.value R h2 1 1 0%N U Full hU hFull
    (@current_boundary R h2 1 0%N U hU (T b)) id hImage
    (@halfline_inclusion_smooth R) halfline_boundary_support_proper=
    @full_dirac_current R h2 1 (euclidean_one_embed b).
Proof.
have hc:U (euclidean_one_embed b).
  by change (is_true (0<euclidean_one_project (euclidean_one_embed b)));
  rewrite euclidean_one_embedK;exact:hb.
pose hPoint:=@current_point_support_proper R h2 1 1 U Full hU
  (euclidean_one_embed b) hc id hImage.
have hEqual:=@current_pushforward_current_congruence R h2 1 1 0%N U Full hU hFull
  id hImage (@halfline_inclusion_smooth R)
  (@current_boundary R h2 1 0%N U hU (T b))
  (@dirac_current R h2 1 U hU (euclidean_one_embed b))
  halfline_boundary_support_proper hPoint (@halfline_current_boundary R h2 b).
exact:(eq_trans hEqual (eq_trans
  (@current_pushforward_dirac R h2 1 1 U Full hU hFull (euclidean_one_embed b)
    hc id hImage (@halfline_inclusion_smooth R))
  (@dirac_current_full_agreement R h2 1 (euclidean_one_embed b)))).
Qed.

(** Source for [halfline_left_primitive_pushed_boundary]:
    the displayed original S has exactly
    the pushed boundary of T, Federer
    4.1.7, p. 359. The two
    actual full-domain point-current definitions agree. *)
Theorem halfline_left_primitive_pushed_boundary:
  @current_boundary R h2 1 0%N Full hFull (S b)=
  @CurrentPushforward.value R h2 1 1 0%N U Full hU hFull
    (@current_boundary R h2 1 0%N U hU (T b)) id hImage
    (@halfline_inclusion_smooth R) halfline_boundary_support_proper.
Proof.
rewrite halfline_boundary_pushforward;exact:halfline_left_primitive_boundary.
Qed.

(** Source for [halfline_left_primitive_support_obstruction]:
    the displayed original primitive has support
    outside f(spt T), Federer 4.1.7,
    p. 359. The proof uses
    its proved boundary, exact spt T
    and the original compact-boundary obstruction. *)
Theorem halfline_left_primitive_support_obstruction:
  ~supportR (S b) `<=` (id @` supportU (T b)).
Proof.
move=>hSupport.
have hCoordinate:forall x,supportR (S b) x->0<x ord0<=b.
  move=>x hx.
  have [y hy hxy]:=hSupport x hx.
  have hSame:y=x:=hxy.
  have hUpper:=@halfline_current_support_upper R h2 b y hy.
  by rewrite hSame in hUpper.
have hImpossible:=@halfline_current_supported_primitive_impossible R h2 b hb (S b) hCoordinate.
apply:hImpossible.
exact:(eq_trans (@halfline_left_primitive_boundary R h2 b)
  (esym (@dirac_current_full_agreement R h2 1 (euclidean_one_embed b)))).
Qed.
End HalflineCurrentExample.
