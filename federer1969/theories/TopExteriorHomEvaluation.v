(** Federer (1969), 3.2.28(2), printed p. 264:
    Hom(Lambda^m R^m,Lambda^m R^n) is isometric to
    Lambda^m R^n by evaluation at any unit top vector.
    Prove the metric and both bijectivity laws on the
    actual exterior powers, including m=0. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerProductUP InnerNorm
  OrthonormalFamilies InnerExterior InnerExteriorPositivity ExteriorGrading
  ExteriorNorm ExteriorHomInner FiniteExteriorPowers FiniteOrdinalBasis
  TopExteriorNorm HomUnitLineEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section TopEvaluation.
Variable R:realType.
Variable h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation V:=(exterior_power (R_n R m) m).
Local Notation W:=(exterior_power (R_n R n) m).
Local Notation BV:=(@exterior_inner_form R h2 (R_n R m)
  (@euclidean_inner_product R m) (@euclidean_inner_productP R m) m).
Local Notation BW:=(@exterior_inner_form R h2 (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m).
Local Notation hV:=(exterior_inner_productP h2 (@euclidean_inner_productP R m) m).
Local Notation hW:=(exterior_inner_productP h2 (@euclidean_inner_productP R n) m).
Variable z:V.
Hypothesis hz:exterior_norm h2 (@euclidean_inner_productP R m) z= 1.

(** Source for [unit_top_exterior_spans]: the top exterior
    source is one-dimensional, 1.3.4, p. 16, used in
    the evaluation isometry of Federer 3.2.28(2), p. 264.
    A unit vector is nonzero even in degree zero. *)
Lemma unit_top_exterior_spans:forall x:V,exists c:R,x=c*:z.
Proof.
have hNz:z!=0.
  apply/eqP=>hZero; move:hz; rewrite hZero exterior_norm_zero=>/eqP.
  by rewrite eq_sym oner_eq0.
exact:(@nonzero_top_vector_spans R h2 (R_n R m) m
  (@coordinate_basis R m) (@coordinate_basisP R m) z hNz).
Qed.

(** Source for [top_exterior_hom_evaluation_inner]: the exact
    isometry displayed in Federer 3.2.28(2), p. 264,
    by 1.7.9, p. 35. Evaluation at any unit top
    vector preserves inner products of all linear maps. *)
Theorem top_exterior_hom_evaluation_inner (f g:Hom V W):
  exterior_hom_inner h2 (@euclidean_inner_productP R m)
    (@euclidean_inner_productP R n) (@coordinate_basisP R m) m f g=
      BW (f z) (g z).
Proof.
apply:hom_unit_line_evaluation_inner; first exact hz.
exact:unit_top_exterior_spans.
Qed.

(** Source for [top_exterior_hom_evaluation_injective]: the
    displayed evaluation map in Federer 3.2.28(2), p. 264,
    is injective because the unit top vector spans its source. *)
Lemma top_exterior_hom_evaluation_injective:
  injective (fun f:Hom V W=>f z).
Proof.
move=>f g he; apply:hom_ext=>x.
have [c ->]:=unit_top_exterior_spans x.
rewrite !linearZ.
change (c*:f z=c*:g z).
by rewrite he.
Qed.

(** Source for [top_exterior_hom_evaluation_surjective]:
    every target exterior vector occurs under evaluation,
    completing the linear isomorphism of Federer 3.2.28(2),
    p. 264. The local rank-one witness uses only
    the unit-source inner-coordinate law of 1.7.1, p. 28. *)
Lemma top_exterior_hom_evaluation_surjective:
  forall w:W,exists f:Hom V W,f z=w.
Proof.
move=>w.
pose F (x:V):W:=(inner_coordinate hV z x)*:w.
have hF:linear F.
  move=>a x y; rewrite /F linearP scalerDl scalerA; reflexivity.
exists (@HomMap R V W F (introT (asboolP _) hF)).
change ((inner_coordinate hV z z)*:w=w).
have hzN:inner_norm hV z= 1:=hz.
rewrite inner_coordinateE -[BV z z](inner_norm_sqr hV) hzN expr1n scale1r.
reflexivity.
Qed.
End TopEvaluation.
