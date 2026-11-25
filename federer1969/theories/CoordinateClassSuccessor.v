(** Federer (1969), 4.1.2, p. 347: continuous
    coordinate kernel derivatives give successive smoothness
    of the convolution. This adapter reuses the actual
    coordinate differentiability criterion of 3.1.1, p. 211,
    and the higher-field class laws of 3.1.11, p. 221. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP NormOpenDomainLaws NormPartialDerivative
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanCoordinateMetric
  FamilyUpdate ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearOne ContinuousMultilinearSealed
  ContinuousMultilinearScalarLift NormHigherDifferentialUP NormHigherDifferentialFirst NormClassHigherFromDerivative NormRegularity
  NormRegularityLinearMaps NormRegularityFiniteSum ContinuousPartialDifferentiability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CoordinateClassSuccessor.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y N NY hN hNY).
Local Notation ez := (fun j=>@ContinuousMultilinear.evaluation R j X Y N NY hN hNY).
Local Notation ZN := (fun j=>@ContinuousMultilinear.norm R j X Y N NY hN hNY).
Local Notation hZ := (fun j=>@ContinuousMultilinear.laws R j X Y N NY hN hNY).
Local Notation hN1 := (continuous_multilinear_norm_is_norm hNY (hZ 1%N)).

(** Source for [coordinate_first_form_lifts_exist]: bounded
    linear assembly of the coordinate differential coefficients,
    Federer 3.1.1, p. 211, reused in the
    regularisation argument of 4.1.2, p. 347. *)
Lemma coordinate_first_form_lifts_exist:
  exists L:'I_n->Hom Y (Z 1%N),
    forall i,(forall y u,@ez 1%N u (L i y)=(u ord0 i)*:y) /\
      norm_bounded_linear NY (@ZN 1%N) (L i).
Proof.
have hFor i:exists L:Hom Y (Z 1%N),
    (forall y u,@ez 1%N u (L y)=(u ord0 i)*:y) /\
      norm_bounded_linear NY (@ZN 1%N) L.
  apply:(@continuous_multilinear_scalar_lift_exists R 1%N X Y (Z 1%N)
  N NY hNY (@ez 1%N) (@ZN 1%N) (hZ 1%N) (fun u=>(u ord0 i:R^o))).
  split.
  - move=>u j c x y; rewrite (ord1 j) !family_with_in.
    change ((c*:x+y) i=c*x i+y i); by rewrite !ffunE.
  - exists 1; split; first exact:ler01.
    move=>u; rewrite big_ord1 mul1r.
    exact:euclidean_coordinate_norm_bound.
have [L hL]:=choice (fun i:'I_n=>@hFor i).
exists L; exact hL.
Qed.

(** Source for [norm_class_successor_coordinate_fields]: class
    k of the actual coordinate partials and continuity
    of f imply class k+1 of f, by
    Federer 3.1.1, p. 211, and 3.1.11,
    p. 221. This is the finite
    reconstruction used after convolution differentiation in 4.1.2. *)
Theorem norm_class_successor_coordinate_fields (f:X->Y) (p:'I_n->X->Y) k:
  norm_class_zero N NY (fun _=>True) f ->
  (forall a i,has_norm_partial_derivative NY f a i (p i a)) ->
  (forall i,norm_class hN hNY (fun _=>True) (p i) k) ->
  norm_class hN hNY (fun _=>True) f k.+1.
Proof.
move=>hF hp hClass.
have [L hL]:=coordinate_first_form_lifts_exist.
pose G:=fun a:X=>\sum_i L i (p i a).
pose op:=@continuous_multilinear_one_operator R X Y (Z 1%N) N NY
  (@ez 1%N) (@ZN 1%N) (hZ 1%N).
have hBasis a j:op (G a) (@coordinate_basis R n j)=p j a.
  change (@ez 1%N [ffun _:'I_1=>@coordinate_basis R n j] (G a)=p j a).
  rewrite /G linear_sum (bigD1 j) //=.
  rewrite (hL j).1 !ffunE eqxx scale1r.
  rewrite big1 ?addr0 //.
  move=>i hi; rewrite (hL i).1 !ffunE (negbTE hi) scale0r.
  reflexivity.
have hDifferential a:has_norm_differential N NY (fun _=>True) f a (op (G a)).
  apply:(@continuous_partials_differential R n Y NY hNY (fun _=>True) f a p (op (G a))
    (hBasis a)).
  - exists 1; split; first exact:ltr01.
    move=>x _; split; first exact:Logic.I.
    move=>i; exact:hp.
  - move=>i e he.
    have [d [hd hBound]]:=(@norm_class_continuous R X Y N NY hN hNY (fun _=>True) (p i) k (hClass i) a Logic.I).2 e he.
    exists d; split=>// x _ hx.
    have hPoint:=hBound (x-a) Logic.I hx.
    have hShift:a+(x-a)=x by rewrite addrC subrK.
    by rewrite hShift in hPoint.
have hG:norm_class hN hN1 (fun _=>True) G k.
  apply:(@norm_class_finite_sum R X (Z 1%N) N (@ZN 1%N) hN hN1
    (fun _=>True) (Finite.clone 'I_n _) (fun i a=>L i (p i a)) k
    (fun a _=>norm_full_domain_interior N a)).
  move=>i; exact:(@norm_class_postcompose_linear R X Y (Z 1%N) N NY (@ZN 1%N)
    hN hNY hN1 (fun _=>True) (p i) (L i) k (hL i).2 (hClass i)).
pose W j:=@ContinuousMultilinear.space R j X (Z 1%N) N (@ZN 1%N) hN hN1.
pose ew j:=@ContinuousMultilinear.evaluation R j X (Z 1%N) N (@ZN 1%N) hN hN1.
pose WN j:=@ContinuousMultilinear.norm R j X (Z 1%N) N (@ZN 1%N) hN hN1.
pose hW j:=@ContinuousMultilinear.laws R j X (Z 1%N) N (@ZN 1%N) hN hN1.
have hHigher a (_:True):has_norm_higher_differential N ez ZN (fun _=>True) f 1%N a (G a).
  exact:(@norm_higher_differential_first R X Y N NY hN hNY Z ez ZN hZ
    (fun _=>True) f a (G a)).2 (hDifferential a).
exact:(@norm_class_higher_first_field_iff R k X Y N NY hN hNY
  Z ez ZN hZ W ew WN hW (fun _=>True) f G hF hHigher).2 hG.
Qed.
End CoordinateClassSuccessor.
