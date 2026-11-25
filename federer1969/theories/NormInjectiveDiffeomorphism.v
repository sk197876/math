(** Federer (1969), 3.1.18, p. 229: the local diffeomorphism obtained
    from the inverse-function theorem. This supporting theorem builds
    the inverse of an injective class-k map from actual image points;
    its regularity follows from 3.1.1 and 3.1.11, not an inverse premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP RealNormUP NormMetric CompleteMetricUP
  NormDifferentialUP NormClassOneUP NormClassOneInverse NormRegularity
  NormRegularityOperations NormDiffeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_injective_diffeomorphism_exists]: supporting the
    source change g restricted to U in Federer 3.1.18, p. 229. A
    one-to-one class-k map with invertible continuous differentials has
    a class-k inverse on its actual image. Completeness is the hypothesis
    of the already proved inverse-function theorem. *)
Theorem norm_injective_diffeomorphism_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX)
    (hcomplete:is_complete_metric_space (real_norm_metric_space hNX))
    (A:set X) (f:X->X) (D E:X->Hom X X) k :
  norm_class hNX hNX A f k -> is_norm_class_one_field NX NX A f D ->
  (forall x, A x -> norm_bounded_linear NX NX (E x)) ->
  (forall x, A x -> cancel (D x) (E x)) ->
  (forall x, A x -> cancel (E x) (D x)) ->
  (forall x y, A x -> A y -> f x=f y -> x=y) ->
  exists g:X->X, is_norm_diffeomorphism hNX hNX A (f @` A) f g k.
Proof.
move=>hf hD hE hED hDE hinj.
pose P y := exists x, A x /\ f x=y.
pose g (y:X) : X :=
  match pselect (P y) with
  | left h=>projT1 (cid h)
  | right _=>0
  end.
have hgmap y (hy:(f @` A) y) : A (g y) /\ f (g y)=y.
  have hP:P y by have [x hx he] := hy; exists x.
  rewrite /g; case: (pselect (P y))=>[hp|hp]; last by exfalso; exact: hp hP.
  by case: (cid hp).
have hfmap x (hx:A x) : (f @` A) (f x) by exists x.
have hgf x (hx:A x) : g (f x)=x.
  have [hAg he] := hgmap (f x) (hfmap x hx).
  exact: hinj (g (f x)) x hAg hx he.
have hg1 : norm_class_one NX NX (f @` A) g.
  apply: (@norm_class_one_inverse R X X NX NX hNX hNX hcomplete A (f @` A)
    f g D E hD hE hED hDE).
  - move=>x hx; exact: conj (hfmap x hx) (hgf x hx).
  - exact hgmap.
have hgfirst := (@norm_class_firstP R X X NX NX hNX hNX (f @` A) g).2 hg1.
have hgk := norm_class_inverse_from_first hfmap (fun y hy=>(hgmap y hy).1)
  hgf (fun y hy=>(hgmap y hy).2) hf hgfirst.
exists g; constructor=>//.
- pose I := hom_of_linear (linear_id X).
  have hI:norm_bounded_linear NX NX I.
    exists 1; split; first exact: ler01.
    by move=>x; change (NX x<=1*NX x); rewrite mul1r.
  exists I,I; split=>//; split=>//; split; by move=>x.
- by move=>y hy; exact: (hgmap y hy).1.
- by move=>y hy; exact: (hgmap y hy).2.
Qed.
