(** Federer (1969), 3.2.47, p. 282: regularity of the
    exact positively normalized recurrence. The proof uses only
    public recurrence laws; no continuity of a chosen implementation
    or an arbitrarily signed orthonormalisation is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP
  InnerProductUP InnerNorm InnerNormalization OrthonormalFamilies OrthonormalProjection
  HilbertFormCompactness FinitePrefixes PositiveGramSchmidtUP
  NormRegularity NormRegularityOperations NormRegularityBilinear
  NormRegularityFiniteSum InnerNormalizationSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_gram_schmidt_norm_class]: the actual
    family given by the recurrence of 3.2.47, p. 282,
    has every finite class possessed by its input family. The
    recurrence and nonzero residuals are independent mathematical
    laws discharged by the sealed operator at the application. *)
Theorem positive_gram_schmidt_norm_class (R:realType) (X V:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) B (hB:@is_inner_product R V B)
    n (A:X->Prop) (Q F:'I_n->X->V) k:
  (forall x,A x->is_positive_gram_schmidt hB (fun i=>Q i x) (fun i=>F i x)) ->
  (forall i,norm_class hNX (inner_norm_real_norm hB) A (Q i) k) ->
  forall i,norm_class hNX (inner_norm_real_norm hB) A (F i) k.
Proof.
move=>hRecurrence hQ.
pose N:=inner_norm hB.
pose hN:=inner_norm_real_norm hB.
pose hAbs:=scalar_absolute_value_norm R.
have hInduction:forall b (i:'I_n),(val i<b)%N ->norm_class hNX hN A (F i) k.
  elim=>[|b ih] i hi; first by rewrite ltn0 in hi.
  case:(ltnP (val i) b)=>hib; first exact:ih i hib.
  have hiEq:val i=b by apply/eqP; rewrite eqn_leq hib -ltnS hi.
  have hPrevious (j:'I_(val i)):
      norm_class hNX hN A (F (widen_ord (ltnW (ltn_ord i)) j)) k.
    apply:ih; change ((val j<b)%N); by rewrite -hiEq; exact:ltn_ord.
  have hOpen x (hx:A x):norm_domain_interior NX A x.
    exact ((@norm_class_continuous R X V NX N hNX hN A (Q i) k (hQ i) x hx).1).
  pose P:=fun x=>\sum_(j:'I_(val i))
    B (Q i x) (F (widen_ord (ltnW (ltn_ord i)) j) x)*:
      F (widen_ord (ltnW (ltn_ord i)) j) x.
  have hProjection:norm_class hNX hN A P k.
    apply:(norm_class_finite_sum hOpen)=>j.
    have hCoefficient:=@norm_class_bilinear R X V V R^o NX N N (fun t:R^o=>`|t|)
      hNX hN hN hAbs A (Q i) (F (widen_ord (ltnW (ltn_ord i)) j)) B k
      (inner_product_norm_bounded_bilinear hB) (hQ i) (hPrevious j).
    exact (@norm_class_scalar_product R X V NX N hNX hN A
      (fun x=>B (Q i x) (F (widen_ord (ltnW (ltn_ord i)) j) x))
      (F (widen_ord (ltnW (ltn_ord i)) j)) k hCoefficient (hPrevious j)).
  pose r:=fun x=>positive_gram_schmidt_residual hB
    (fun j=>Q j x) (fun j=>F j x) i.
  have hDifference:=norm_class_subtract (hQ i) hProjection.
  have hResidual:norm_class hNX hN A r k.
    apply:(norm_class_domain_agreement _ hDifference)=>x hx.
    rewrite /r /P /positive_gram_schmidt_residual /orthonormal_projection.
    congr (Q i x-_); apply:eq_bigr=>j _.
    by rewrite /family_prefix inner_coordinateE.
  have hNonzero x (hx:A x):r x!=0.
    exact (@positive_gram_schmidt_nonzero R V B hB n
      (fun j=>Q j x) (fun j=>F j x) (hRecurrence x hx) i).
  have hNormalized:=inner_normalize_norm_class hResidual hNonzero.
  apply:(norm_class_domain_agreement _ hNormalized)=>x hx.
  exact (esym (@positive_gram_schmidt_equation R V B hB n
    (fun j=>Q j x) (fun j=>F j x) (hRecurrence x hx) i)).
move=>i; exact:hInduction n i (ltn_ord i).
Qed.

(** Source for [positive_gram_schmidt_all_orders]: the smooth
    positive recurrence used for the section F in 3.2.47,
    p. 282. All derivatives are consequences of the exact
    finite recurrence and prior scalar and bilinear calculus. *)
Corollary positive_gram_schmidt_all_orders (R:realType) (X V:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) B (hB:@is_inner_product R V B)
    n (A:X->Prop) (Q F:'I_n->X->V):
  (forall x,A x->is_positive_gram_schmidt hB (fun i=>Q i x) (fun i=>F i x)) ->
  (forall i,norm_class_all_orders hNX (inner_norm_real_norm hB) A (Q i)) ->
  forall i,norm_class_all_orders hNX (inner_norm_real_norm hB) A (F i).
Proof.
move=>hRecurrence hQ i k.
exact (@positive_gram_schmidt_norm_class R X V NX hNX B hB n A Q F k
  hRecurrence (fun j=>hQ j k) i).
Qed.
