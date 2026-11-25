(** Federer (1969), 3.1.15, p. 227:
    the top differential D^k f is differentiable wherever all its
    coordinates D^alpha f are, since D^k f is recovered from them by
    the bounded linear reconstruction of 3.1.11, p. 223; together with
    Stepanoff's theorem this gives L^m(A-dmn D D^k f)=0. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology functions.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness RealNormUP
  EuclideanLebesgueDimensions NormDifferentialUP NormDifferentialLocal NormDifferentialFiniteCalculus
  NormClassOneUP ContinuousMultilinearUP ContinuousMultilinearNorm NormHigherDifferentialUP
  SymmetricMultiIndices NormHigherMultiPartialUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  TopDifferentialStepanoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Section FromCoordinates.
Variable R : realType.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) (R_n R n).
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space N NY (@ev i) (@ZN i).
Variable k : nat.
Variable B : set X.
Variable f : X->R_n R n.
Variable Dk : X->Z k.
Hypothesis hDkf : forall x, B x -> has_norm_higher_differential N ev ZN B f k x (Dk x).
Hypothesis hDk : norm_class_zero N (@ZN k) B Dk.
Variable iota : symmetric_indices m k->Hom (R_n R n) (Z k).
Hypothesis hiota_bound : forall alpha, norm_bounded_linear NY (@ZN k) (iota alpha).
Hypothesis hiota_rec : forall (A : X->Prop) (g : X->R_n R n) (a : X) (z : Z k),
  has_norm_higher_differential N ev ZN A g k a z ->
  z=\sum_alpha iota alpha (@ev k (norm_multi_partial_arguments R alpha) z).
Let hZNk : is_real_norm (@ZN k) := continuous_multilinear_norm_is_norm hNY (@hZ k).

(** Source for [top_differential_from_coordinates]:
    D^k f=sum_alpha iota_alpha o D^alpha f on the domain, so D^k f is
    differentiable at every point where all D^alpha f are,
    Federer 3.1.1(5), p. 210, and 3.1.11, p. 223. *)
Theorem top_differential_from_coordinates (a : X) : B a ->
  (forall alpha, norm_differentiable_at N NY B (top_coordinate ev Dk alpha) a) ->
  norm_differentiable_at N (@ZN k) B Dk a.
Proof.
move=>ha hdiff.
have [L hL] := choice hdiff.
have hfs : forall (I : finType) (F : I->X->Z k) x, (\sum_i F i) x=\sum_i F i x.
  by move=>I F x; elim/big_ind2: _=>[|p q u v hp hu|i _] //; rewrite -hp -hu.
have hsum := norm_differential_finite_sum hN hZNk (A:=B) (a:=a) (P:=predT)
  (f:=fun alpha x=>iota alpha (top_coordinate ev Dk alpha x))
  (L:=fun alpha=>hom_comp (iota alpha) (L alpha)) (hDk ha).1
  (fun alpha _=>norm_differential_postcompose hN (hL alpha) (hiota_bound alpha)).
exists (\sum_(alpha | predT alpha) hom_comp (iota alpha) (L alpha)).
apply: (norm_differential_domain_agreement hN _ hsum)=>x hx.
rewrite hfs; exact: esym (hiota_rec (hDkf hx)).
Qed.

(** Source for [top_differential_almost_everywhere]:
    L^m(A-dmn D D^k f)=0 by Stepanoff's theorem 3.1.9, Federer 3.1.15,
    p. 227. *)
Theorem top_differential_almost_everywhere (A : set X) : A `<=` B -> open B ->
  (forall a, A a -> exists M r : R, 0<r /\
    forall x, B x -> N (x-a)<r -> @ZN k (Dk x-Dk a)<=M*N (x-a)) ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) A
    [set a | norm_differentiable_at N (@ZN k) B Dk a].
Proof.
move=>hAB hB hgrowth.
have hae := top_coordinates_differentiable_almost_everywhere hZ hAB hB hgrowth.
apply: (measure_almost_everywhere_on_implication _ _ _).2.
apply: (measure_almost_everywhere_mono (euclidean_lebesgue_is_measure R m) _
  ((measure_almost_everywhere_on_implication _ _ _).1 hae)).
move=>a ha haA; exact: (top_differential_from_coordinates (hAB a haA) (ha haA)).
Qed.
End FromCoordinates.
