(** Federer (1969), 3.3.19, p. 305: the actual
    circular cap direction count has the complementary
    lower bound in every original orientation. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerProductUP Bilinear InnerNorm InnerMetric
  RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed CircularUnitVectors CircularRegularDirections
  CircularRegularCapCount.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Section Count.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation hE:=(@euclidean_inner_productP R 2).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation p:=(@CircularTrigonometry.half_period R).

(** Source for [circular_cosine_semicircle_reflection]: the
    actual cos(pi-gamma)=-cos(gamma) identity used in
    the complementary cap count for 3.3.19, p. 305. *)
Lemma circular_cosine_semicircle_reflection (gamma:R):C (p-gamma)=-C gamma.
Proof.
by rewrite circular_cosine_difference (circular_trig_cosine_pi (@CircularTrigonometry.laws R))
  (circular_trig_sine_pi (@CircularTrigonometry.laws R)) mul0r addr0 mulN1r.
Qed.

(** Source for [circular_regular_cap_containing_count]: if
    a subfamily contains every actual original direction
    in the cap of half-angle gamma, its fraction is at
    least gamma/pi-1/n. Combined with the upper count,
    this proves uniform circular distribution needed in
    3.3.19, p. 305. Zero and full half-angles remain. *)
Theorem circular_regular_cap_containing_count n (u:E) (gamma:R) (F:{fset 'I_n}):
  (0<n)%N ->inner_norm hE u= 1 ->0<=gamma ->gamma<=p ->
  (forall k,C gamma<=euclidean_inner_product (@circular_regular_direction R n k) u ->k \in F) ->
  gamma/p-1/n%:R<=#|` F|%:R/n%:R.
Proof.
move=>hn hu hGamma hGammaP hContains.
have hp:= real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R)).
have hpN:p!=0 by rewrite gt_eqF.
have hNP:(0<n%:R:>R) by rewrite ltr0n.
have hNN:(n%:R:R)!=0 by rewrite gt_eqF.
pose U:{fset 'I_n}:=[fset k | k:'I_n].
pose G:{fset 'I_n}:=(U `\` F)%fset.
have hU k:k \in U by apply/imfsetP;by exists k.
have hNegativeUnit:inner_norm hE (-u)= 1 by rewrite inner_normN hu.
have hComplement k:k \in G ->C (p-gamma)<=euclidean_inner_product (@circular_regular_direction R n k) (-u).
  move=>hk;move:hk;rewrite /G in_fsetD=>/andP[hNotF _].
  have hNotCoordinate:~(C gamma<=euclidean_inner_product (@circular_regular_direction R n k) u).
    move=>hCoordinate;have hF:= hContains k hCoordinate.
    by move:hNotF;rewrite hF.
  have hCoordinate:euclidean_inner_product (@circular_regular_direction R n k) u<C gamma.
    rewrite ltNge;exact/negP.
  have hZero:(-u:E)= 0-u by rewrite sub0r.
  rewrite circular_cosine_semicircle_reflection hZero
    (bilBr (inner_bilinear hE)) (bil0r (inner_bilinear hE)) sub0r.
  by rewrite lerN2;exact:ltW hCoordinate.
have hComplementNonnegative:0<=p-gamma by lra.
have hComplementUpper:p-gamma<=p by lra.
have hCount:= @circular_regular_cap_subfamily_count R n (-u) (p-gamma) G
  hn hNegativeUnit hComplementNonnegative hComplementUpper hComplement.
have hIntersection:(U `&` F)%fset= F.
  apply/fsetP=>k;by rewrite in_fsetI (hU k) andTb.
have hCard:= cardfsID F U.
rewrite hIntersection -/G in hCard.
have hTotal:#|` U|= n by rewrite /U card_imfset //= -cardE card_ord.
rewrite hTotal in hCard.
have hReal:(#|` F|%:R+#|` G|%:R=(n%:R:R)) by rewrite -natrD hCard.
have hFraction:#|` F|%:R/n%:R+#|` G|%:R/n%:R=(1:R).
  by rewrite -mulrDl hReal divff.
have hComplementFraction:(p-gamma)/p= 1-gamma/p by field.
rewrite hComplementFraction in hCount;nra.
Qed.
End Count.
