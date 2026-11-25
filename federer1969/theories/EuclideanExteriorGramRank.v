(** Federer (1969), 3.2.33, p. 270: h_i is
    the Hilbert inner square of the actual i-th exterior
    differential, using 1.7.9, p. 35. Its vanishing
    and positivity detect actual rank. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps
  InnerProductUP InnerProductLaws InnerExterior InnerExteriorPositivity ExteriorGrading ExteriorMaps
  FiniteExteriorPowers FiniteOrdinalBasis ExteriorIndices HomInner
  LinearRankUP LinearRankAtLeast LinearRankExterior.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Gram.
Variable R:realType.
Variables m n q:nat.
Local Notation h2:=(euclidean_two_nonzero R).
Local Notation ES:=(exterior_power (R_n R m) q).
Local Notation ET:=(exterior_power (R_n R n) q).
Local Notation BS:=(@exterior_inner_form R h2 (R_n R m) (@euclidean_inner_product R m) (@euclidean_inner_productP R m) q).
Local Notation BT:=(@exterior_inner_form R h2 (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n) q).
Local Notation hS:=(@exterior_inner_productP R h2 (R_n R m) (@euclidean_inner_product R m) (@euclidean_inner_productP R m) q).
Local Notation hT:=(@exterior_inner_productP R h2 (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n) q).
Local Notation hb:=(finite_ordinal_basis (@finite_e_lambda_basis R m (R_n R m)
  (@coordinate_basis R m) (@coordinate_basisP R m) h2 q)).

(** Source for [euclidean_exterior_gram]: exactly the
    displayed h_i=exterior_i(Df) dot exterior_i(Df)
    in Federer 3.2.33, p. 270. This is the
    Hilbert Hom inner product of 1.7.9, not the
    squared exterior operator norm or mass norm. The
    existing abstract exterior and inner-product interfaces
    determine it, including degree zero and zero spaces. *)
Definition euclidean_exterior_gram (L:Hom (R_n R m) (R_n R n)):R:=
  hom_inner hS hT hb (hom_of_linear (exterior_power_map (hom_as_linear L) q))
    (hom_of_linear (exterior_power_map (hom_as_linear L) q)).

(** Source for [euclidean_exterior_gram_nonnegative]: the
    actual h_i in Federer 3.2.33, p. 270, is
    nonnegative by the inner-product laws, including all
    natural degrees beyond the ambient dimensions. *)
Lemma euclidean_exterior_gram_nonnegative (L:Hom (R_n R m) (R_n R n)):
  0<=euclidean_exterior_gram L.
Proof.
exact:(inner_nonnegative (hom_inner_productP hS hT hb)
  (hom_of_linear (exterior_power_map (hom_as_linear L) q))).
Qed.

(** Source for [euclidean_exterior_gram_zero_iff]: the
    equality h_(mu+1)= 0 in the description of S,
    Federer 3.2.33, p. 270. Hilbert definiteness
    says the actual exterior operator vanishes; the
    proved exterior rank test identifies the exact rank
    threshold. No Jacobian or rank premise is added. *)
Theorem euclidean_exterior_gram_zero_iff (L:Hom (R_n R m) (R_n R n)):
  euclidean_exterior_gram L= 0 <->~linear_rank_at_least L q.
Proof.
pose M:=hom_of_linear (exterior_power_map (hom_as_linear L) q).
have hEq:(euclidean_exterior_gram L== 0)=(M== 0).
  exact:(inner_self_eq0 (hom_inner_productP hS hT hb) M).
have hRank:=@linear_rank_exteriorP R h2 (R_n R m) (R_n R n) m
  (@coordinate_basis R m) (@coordinate_basisP R m) L q.
split.
- move=>/eqP; rewrite hEq=>/eqP hZero hR.
  have [xi hXi]:=hRank.1 hR.
  have hValue:=congr1 (fun F:Hom ES ET=>F xi) hZero.
  change (exterior_power_map (hom_as_linear L) q xi= 0) in hValue.
  by rewrite hValue eqxx in hXi.
- move=>hNoRank.
  have hZero:M= 0.
    apply:hom_ext=>xi; change (exterior_power_map (hom_as_linear L) q xi= 0).
    apply/eqP; apply/negPn/negP=>hn.
    apply:hNoRank; apply:hRank.2; by exists xi.
  apply/eqP; by rewrite hEq hZero eqxx.
Qed.

(** Source for [euclidean_exterior_gram_positive_iff]: the
    condition h_mu>0 in Federer 3.2.33, p. 270,
    is exactly rank at least mu. This preserves the
    degree-zero scalar convention and singular operators. *)
Theorem euclidean_exterior_gram_positive_iff (L:Hom (R_n R m) (R_n R n)):
  0<euclidean_exterior_gram L <->linear_rank_at_least L q.
Proof.
split.
- move=>hp; apply:contrapT=>hNo.
  have hZero:=(euclidean_exterior_gram_zero_iff L).2 hNo.
  by rewrite hZero ltxx in hp.
- move=>hRank; rewrite lt_def (euclidean_exterior_gram_nonnegative L) andbT.
  apply/negP=>/eqP hz; exact:((euclidean_exterior_gram_zero_iff L).1 hz hRank).
Qed.
End Gram.

(** Source for [euclidean_exterior_gram_exact_rank]: the
    displayed equality S={h_mu>0=h_(mu+1)} in Federer
    3.2.33, p. 270. The original image-basis rank
    and both actual Hilbert exterior-Gram tests are equivalent,
    without a selected image basis or an ambient degree bound. *)
Theorem euclidean_exterior_gram_exact_rank (R:realType) m n mu
    (L:Hom (R_n R m) (R_n R n)):
  has_linear_rank L mu <->
  0<euclidean_exterior_gram mu L /\euclidean_exterior_gram mu.+1 L= 0.
Proof.
split.
- move=>hRank; split.
  + apply:(euclidean_exterior_gram_positive_iff mu L).2.
    exact:(linear_rank_at_leastP mu hRank).2 (leqnn mu).
  + apply:(euclidean_exterior_gram_zero_iff mu.+1 L).2=>hNext.
    have hBad:=(linear_rank_at_leastP mu.+1 hRank).1 hNext.
    by rewrite ltnn in hBad.
- move=>[hLow hHigh].
  have [r [hRank hBound]]:=linear_rank_exists L (@coordinate_basisP R n).
  have hMu:(mu<=r)%N:=(linear_rank_at_leastP mu hRank).1
    ((euclidean_exterior_gram_positive_iff mu L).1 hLow).
  have hr:(r<=mu)%N.
    rewrite leqNgt; apply/negP=>hAbove.
    apply:((euclidean_exterior_gram_zero_iff mu.+1 L).1 hHigh).
    exact:(linear_rank_at_leastP mu.+1 hRank).2 hAbove.
  have he:r=mu by apply/eqP; rewrite eqn_leq hr hMu.
  by rewrite -he.
Qed.
