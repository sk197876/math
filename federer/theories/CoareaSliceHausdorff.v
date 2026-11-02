(** Federer (1969), 3.2.11, p. 249: the
    fixed-coordinate slice of a perturbed fibre has the
    Hausdorff mass of the translated original fibre. Derive
    the isometric image equality from the proved Lipschitz
    image bound in both directions, using the coordinate retraction. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanMetricProduct EuclideanSquaredProduct
  SquaredMetricProductLaws MetricCartesianProductUP LipschitzUP HausdorffMeasure
  HausdorffLipschitzImages MeasureUP MeasureBasic MappingMultiplicity
  CoareaPerturbationMap CoareaCylinderFibres ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_fixed_last_slice_hausdorff]: the
    isometric fibre identification in Federer 3.2.11, p. 249.
    Every fixed-last-coordinate inclusion preserves natural-degree
    Hausdorff mass on every subset, with no measurability or
    finiteness hypothesis and with empty blocks included. *)
Theorem coarea_fixed_last_slice_hausdorff (R:realType) m n d
    (z:inner_metric_space (@euclidean_inner_productP R n)) (A:set (R_n R m)):
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (m+n))) d
    ((fun x=>euclidean_block_join (x,z)) @` A)=
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) d A.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose P:=inner_metric_space (@euclidean_inner_productP R (m+n)).
pose i:=fun x:X=>(euclidean_block_join (x,z):P).
pose p:=fun w:P=>(@euclidean_first_block R m n w:X).
have hSquared:=@euclidean_blocks_are_squared_metric_product R m n.
have hI:is_metric_lipschitz_bound setT i (1:R).
  split; first exact:ler01.
  move=>x y _ _; rewrite mul1r.
  by rewrite (squared_metric_product_first_slice hSquared z x y).
have hP:is_metric_lipschitz_bound setT p (1:R).
  exact (metric_product_first_nonexpanding (@euclidean_blocks_are_metric_product R m n)).
have hCancel:cancel i p.
  move=>x; exact (congr1 fst (@euclidean_block_joinK R m n (x,z))).
have hUpper:=@hausdorff_lipschitz_image_bound R X P i 1%R d hI A.
have hLower:=@hausdorff_lipschitz_image_bound R P X p 1%R d hP (i @` A).
rewrite expr1n mul1e in hUpper hLower.
have hImage:p @` (i @` A)=A.
  apply/seteqP; split=>x.
  - move=>[w [v hv <-] <-]; by rewrite hCancel.
  - move=>hx; exists (i x); first by exists x.
    exact (hCancel x).
rewrite hImage mul1e in hLower.
by apply/eqP; rewrite eq_le hUpper hLower.
Qed.

(** Source for [coarea_double_fibre_mass_inside]: the
    inner Hausdorff mass in Federer 3.2.11, p. 249,
    equals the original fibre mass at y-epsilon*z when
    z belongs to the auxiliary ball. This supporting law
    permits any cylinder factor B and any natural degree. *)
Lemma coarea_double_fibre_mass_inside (R:realType) m n d
    (f:R_n R m->R_n R n) e (A:set (R_n R m)) (B:set (R_n R n)) y z:
  B z ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (m+n))) d
    (mapping_fibre (@euclidean_last_block R m n)
      (mapping_fibre (coarea_perturbation_map f e) (coarea_cylinder A B) y) z)=
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) d
    (mapping_fibre f A ((y-e*:z)%R)).
Proof.
move=>hz; rewrite coarea_perturbation_double_fibre.
have hSet:[set x|A x /\ B z /\ f x=(y-e*:z)%R]=mapping_fibre f A ((y-e*:z)%R).
  apply/seteqP; split=>x.
  - by move=>[hx [_ hf]]; split.
  - move=>[hx hf]; split; first exact hx; by split.
rewrite hSet; exact:coarea_fixed_last_slice_hausdorff.
Qed.

(** Source for [coarea_double_fibre_mass_outside]: the
    complementary zero part of the same sliced integral in
    Federer 3.2.11, p. 249. Outside the auxiliary
    cylinder factor the actual double fibre is empty. *)
Lemma coarea_double_fibre_mass_outside (R:realType) m n d
    (f:R_n R m->R_n R n) e (A:set (R_n R m)) (B:set (R_n R n)) y z:
  ~B z ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (m+n))) d
    (mapping_fibre (@euclidean_last_block R m n)
      (mapping_fibre (coarea_perturbation_map f e) (coarea_cylinder A B) y) z)=0.
Proof.
move=>hz.
have hEmpty:mapping_fibre (@euclidean_last_block R m n)
    (mapping_fibre (coarea_perturbation_map f e) (coarea_cylinder A B) y) z=set0.
  apply/seteqP; split=>w; last by case.
  move=>[[[hA hB] hG] hQ]; exfalso; apply:hz; by rewrite -hQ.
rewrite hEmpty; exact:measure_empty (@hausdorff_measure_is_measure R _ d).
Qed.
