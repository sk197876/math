(** Federer (1969), 3.2.47(1), p. 283: a
    product of two genuinely rectifiable sets is genuinely
    rectifiable in the sum dimension. Positive degrees use
    their actual bounded parameter domains; degree zero uses
    the printed finite-set convention of 3.2.14, p. 252. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanCartesianMap EuclideanMetricProduct
  EuclideanBoundedCartesianProduct EuclideanRectifiableGlobalParametrization
  EuclideanLipschitzRectifiableImage RectifiableSetUP LipschitzUP LipschitzBasic
  LipschitzRectifiableImages CompactSubmanifoldRectifiable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_rectifiable_cartesian_product]: bounded
    product parameters prove the positive-degree case of the
    product observation used in 3.2.47(1), p. 283,
    with no source measurability or closedness hypothesis. *)
Lemma positive_rectifiable_cartesian_product (R:realType) m mu n v
    (E:set (R_n R n)) (Z:set (R_n R v)):
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m.+1 E ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R v)) mu.+1 Z ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R (n+v)))
    (m.+1+mu.+1)%N (euclidean_cartesian_set E Z).
Proof.
move=>hE hZ.
have [A [f [hA [hf hImageA]]]]:=positive_rectifiable_global_parametrization hE.
have [B [g [hB [hg hImageB]]]]:=positive_rectifiable_global_parametrization hZ.
have hBounded:=euclidean_bounded_cartesian_product hA hB.
have hGlobal:=euclidean_cartesian_map_lipschitz hf hg.
have hLocal:@is_metric_lipschitz R
    (inner_metric_space (@euclidean_inner_productP R (m.+1+mu.+1)))
    (inner_metric_space (@euclidean_inner_productP R (n+v)))
    (euclidean_cartesian_set A B) (euclidean_cartesian_map f g).
  have [L [hL hBound]]:=hGlobal; exists L; split; first exact hL.
  exact:metric_lipschitz_bound_restrict (fun x _=>I) hBound.
have hRect:=euclidean_lipschitz_bounded_image_rectifiable hBounded hLocal.
by rewrite euclidean_cartesian_map_image hImageA hImageB in hRect.
Qed.

(** Source for [finite_first_rectifiable_cartesian_product]: a
    finite first factor gives a finite union of isometric
    copies of the second, retaining the printed degree-zero
    boundary in 3.2.47(1), p. 283. *)
Lemma finite_first_rectifiable_cartesian_product (R:realType) mu n v
    (E:set (R_n R n)) (Z:set (R_n R v)):
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) 0 E ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R v)) mu Z ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R (n+v)))
    mu (euclidean_cartesian_set E Z).
Proof.
move=>hE hZ.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose P:=inner_metric_space (@euclidean_inner_productP R (n+v)).
pose row:=fun (w:X) (z:Y)=>(euclidean_block_join (w,z):P).
have hLip w:@is_metric_lipschitz R Y P setT (row w).
  apply:metric_lipschitz_of_bound; split; first exact:ler01.
  move=>x y _ _; rewrite mul1r.
  rewrite -(ler_sqr (@mdist_ge0 R P (row w x) (row w y)) (@mdist_ge0 R Y x y)).
  have hSquare:=@euclidean_block_squared_distance R n v (row w x) (row w y).
  rewrite /row !euclidean_block_joinK /= mdistxx expr0n add0r in hSquare.
  by rewrite hSquare.
have hImage:euclidean_cartesian_set E Z=\bigcup_(w in E) (row w @` Z).
  apply/seteqP; split=>p.
  - move=>[hpE hpZ]; exists (euclidean_block_split p).1; first exact hpE.
    exists (euclidean_block_split p).2; first exact hpZ; exact:euclidean_block_splitK.
  - move=>[w hw [z hz <-]]; change (E (euclidean_block_split (euclidean_block_join (w,z))).1 /\
      Z (euclidean_block_split (euclidean_block_join (w,z))).2).
    by rewrite euclidean_block_joinK; split.
rewrite hImage; apply:(@rectifiable_finite_indexed_union R P mu [the choiceType of X] E
  (fun w=>row w @` Z) hE)=>w hw.
apply:(@rectifiable_lipschitz_image R Y P mu Z (row w) _ hZ).
have [L [hL hBound]]:=hLip w; exists L; split; first exact hL.
exact:metric_lipschitz_bound_restrict (fun x _=>I) hBound.
Qed.

(** Source for [finite_second_rectifiable_cartesian_product]: a
    finite second factor gives a finite union of isometric
    copies of the first, supporting the other degree-zero
    boundary of 3.2.47(1), p. 283. *)
Lemma finite_second_rectifiable_cartesian_product (R:realType) m n v
    (E:set (R_n R n)) (Z:set (R_n R v)):
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m E ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R v)) 0 Z ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R (n+v)))
    m (euclidean_cartesian_set E Z).
Proof.
move=>hE hZ.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose P:=inner_metric_space (@euclidean_inner_productP R (n+v)).
pose column:=fun (w:Y) (z:X)=>(euclidean_block_join (z,w):P).
have hLip w:@is_metric_lipschitz R X P setT (column w).
  apply:metric_lipschitz_of_bound; split; first exact:ler01.
  move=>x y _ _; rewrite mul1r.
  rewrite -(ler_sqr (@mdist_ge0 R P (column w x) (column w y)) (@mdist_ge0 R X x y)).
  have hSquare:=@euclidean_block_squared_distance R n v (column w x) (column w y).
  rewrite /column !euclidean_block_joinK /= mdistxx expr0n addr0 in hSquare.
  by rewrite hSquare.
have hImage:euclidean_cartesian_set E Z=\bigcup_(w in Z) (column w @` E).
  apply/seteqP; split=>p.
  - move=>[hpE hpZ]; exists (euclidean_block_split p).2; first exact hpZ.
    exists (euclidean_block_split p).1; first exact hpE; exact:euclidean_block_splitK.
  - move=>[w hw [z hz <-]]; change (E (euclidean_block_split (euclidean_block_join (z,w))).1 /\
      Z (euclidean_block_split (euclidean_block_join (z,w))).2).
    by rewrite euclidean_block_joinK; split.
rewrite hImage; apply:(@rectifiable_finite_indexed_union R P m [the choiceType of Y] Z
  (fun w=>column w @` E) hZ)=>w hw.
apply:(@rectifiable_lipschitz_image R X P m E (column w) _ hE).
have [L [hL hBound]]:=hLip w; exists L; split; first exact hL.
exact:metric_lipschitz_bound_restrict (fun x _=>I) hBound.
Qed.

(** Source for [genuine_rectifiable_cartesian_product]: the genuine
    product rectifiability used in 3.2.47(1), p. 283,
    for all natural dimensions and arbitrary original sets.
    This is stronger than merely a countable or finite-mass
    almost-cover conclusion, and adds no Borel hypothesis. *)
Theorem genuine_rectifiable_cartesian_product (R:realType) m mu n v
    (E:set (R_n R n)) (Z:set (R_n R v)):
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m E ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R v)) mu Z ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R (n+v)))
    (m+mu)%N (euclidean_cartesian_set E Z).
Proof.
case:m=>[|m]; first exact:finite_first_rectifiable_cartesian_product.
case:mu=>[|mu]; last exact:positive_rectifiable_cartesian_product.
rewrite addn0; exact:finite_second_rectifiable_cartesian_product.
Qed.
