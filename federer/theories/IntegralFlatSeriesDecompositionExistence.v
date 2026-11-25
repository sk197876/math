(** Federer (1969), 4.1.24, p. 382: an
    integral-flat series with summable original sizes has
    original rectifiable decompositions of summable mass
    cost. Choose each pair within a summable positive
    error of its infimum. This is existence only;
    no attaining integral minimum is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentMassSealed NonnegativeSum NonnegativeSumAdd
  NonnegativeGeometricBound RectifiableCurrentApproximationUP IntegralCurrentClassesUP
  IntegralFlatSizeUP IntegralFlatSizeSealed IntegralFlatSeriesDecompositionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section IntegralFlatSeriesDecompositionExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Next:=(@current_space R h2 n U hU m.+1).
Local Notation IF:=(@is_integral_flat_current_supported_in R h2 n U hU m K).
Local Notation Size:=(@IntegralFlatSize.value R h2 n m U hU K).

(** Source for [integral_flat_series_decomposition_with_errors]:
    every prescribed summable positive error family works
    in the original series choice, 4.1.24, p. 382.
    The final cost is still the actual chosen
    mass series, not this auxiliary error bound. *)
Theorem integral_flat_series_decomposition_with_errors
    (v:nat->C) (hV:forall i,IF (v i)) (e:nat->R):
  (forall i,0<e i)->
  (nonnegative_sum setT (fun i=>(Size (v i) (hV i))%:E)< +oo)%E->
  (nonnegative_sum setT (fun i=>(e i)%:E)< +oo)%E->
  exists A:nat->C,exists B:nat->Next,
    @is_integral_flat_series_decomposition R h2 n m U hU K v A B.
Proof.
move=>hE hSizeSum hErrorSum.
have hChoice i:=@integral_flat_size_approximate R h2 n m U hU K
  (v i) (Size (v i) (hV i)) (@IntegralFlatSize.laws R h2 n m U hU K (v i) (hV i))
  (e i) (hE i).
have[A hChoices]:=choice hChoice.
have[B hData]:=choice hChoices.
have hSizePositive i:0<=Size (v i) (hV i).
  exact:integral_flat_size_nonnegative (@IntegralFlatSize.laws R h2 n m U hU K (v i) (hV i)).
have hSizePositiveE i:(0<=(Size (v i) (hV i))%:E)%E.
  rewrite lee_fin;exact:hSizePositive i.
have hErrorPositiveE i:(0<=(e i)%:E)%E.
  rewrite lee_fin;exact:ltW (hE i).
have hFunctions:(fun i=>(Size (v i) (hV i)+e i)%:E)=
    (fun i=>(Size (v i) (hV i))%:E+(e i)%:E)%E.
  by apply:funext=>i;rewrite EFinD.
have hMajorantSum:(nonnegative_sum setT (fun i=>(Size (v i) (hV i)+e i)%:E)< +oo)%E.
  rewrite hFunctions (@nonnegative_sum_add R nat setT
    (fun i=>(Size (v i) (hV i))%:E) (fun i=>(e i)%:E)
    (fun i _=>hSizePositiveE i) (fun i _=>hErrorPositiveE i)).
  exact:lte_add_pinfty hSizeSum hErrorSum.
exists A,B;constructor.
- move=>i;exact:(hData i).1.
- move=>i;exact:(hData i).2.1.
- move=>i;exact:(hData i).2.2.1.
- apply:(le_lt_trans _ hMajorantSum);apply:nonnegative_sum_mono=>i _.
  exact:ltW (hData i).2.2.2.
Qed.

(** Source for [integral_flat_series_decomposition_exists]: the
    original summable-size hypothesis alone gives the
    required summable-cost choice, 4.1.24, p. 382.
    Positive geometric errors are derived internally. *)
Theorem integral_flat_series_decomposition_exists (v:nat->C) (hV:forall i,IF (v i)):
  (nonnegative_sum setT (fun i=>(Size (v i) (hV i))%:E)< +oo)%E->
  exists A:nat->C,exists B:nat->Next,
    @is_integral_flat_series_decomposition R h2 n m U hU K v A B.
Proof.
move=>hSizeSum;pose q:R:=1/2.
have hQ:0<q<1 by rewrite /q;apply/andP;split;lra.
have hPositive:forall i,0<q^+i by move=>i;exact:(exprn_gt0 i (andP hQ).1).
have hErrorSum:(nonnegative_sum setT (fun i=>(q^+i)%:E)< +oo)%E.
  have hBound:=@nonnegative_geometric_bound R 1 q (ler01)
    (ltW (andP hQ).1) (andP hQ).2.
  have hFunctions:(fun i=>(1*q^+i)%:E)=(fun i=>(q^+i)%:E).
    by apply:funext=>i;rewrite mul1r.
  rewrite hFunctions in hBound;exact:(le_lt_trans hBound (ltry _)).
exact:(@integral_flat_series_decomposition_with_errors v hV (fun i=>q^+i)
  hPositive hSizeSum hErrorSum).
Qed.
End IntegralFlatSeriesDecompositionExistence.
