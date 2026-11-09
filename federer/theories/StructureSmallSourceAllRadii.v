(** Federer (1969), 3.3.8, p. 295: the small-diameter
    piece allows the C_j bounds at every positive radius. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNorm EuclideanProjectionSpace
  StructureCone StructureConeUP StructureProjectionKernel StructureProjectionCone
  StructureConeCostBounds StructureApertureClosedSets StructureApertureMassUP
  EuclideanBallVolume MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_small_source_all_radii]: the sentence
    extending 0<r<1/i to all r>0 in Federer 3.3.8, p. 295.
    The original E has a fixed pairwise distance upper bound a
    strictly below delta. An actual intermediate radius encloses
    all of E from every original centre. No closure, measure or
    attainment of the diameter is assumed. *)
Theorem structure_small_source_all_radii (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (a delta t sigma lam:R):
  is_measure phi ->0<=a ->a<delta ->0<sigma<1 ->sigma<t ->0<lam ->
  (forall x y,E x ->E y ->mdist x y<=a) ->
  is_structure_aperture_mass_bound hmn phi
    (E `&` structure_aperture_bound_centres hmn phi E p delta t
      (lam*euclidean_unit_ball_volume R m)) p sigma lam.
Proof.
move=>hPhi ha haDelta hSigma hSigmaT hLam hDiameter.
pose C:=structure_aperture_bound_centres hmn phi E p delta t
  (lam*euclidean_unit_ball_volume R m).
move=>x [hx hC] r hr s hs hsSigma.
have hst:0<s<t by apply/andP; split=>//; exact:le_lt_trans hsSigma hSigmaT.
have hMass q:0<q<delta ->
    (phi (E `&` structure_cone (structure_projection_kernel hmn p) x q%:E s)<=
      (lam*euclidean_unit_ball_volume R m*q^+m*s^+m)%:E)%E.
  move=>hq; exact:((@structure_cone_cost_mass_bound R n m hmn phi E p x q s
    (lam*euclidean_unit_ball_volume R m) (andP hq).1 hs).1 (hC q s hq hst)).
case:(ltP r delta)=>hrDelta.
- apply:le_trans _ (hMass r _); last by apply/andP; split.
  apply:(@measure_mono R _ phi hPhi)=>y [[hy _] hCone]; by split.
pose q:=(a+delta)/2.
have hq:0<q<delta by rewrite /q; apply/andP; split; nra.
have haq:a<q by rewrite /q; nra.
have hqr:q<=r:=le_trans (ltW (andP hq).2) hrDelta.
have hSubset:
    ((E `&` C) `&` structure_cone (structure_projection_kernel hmn p) x r%:E s) `<=`
    (E `&` structure_cone (structure_projection_kernel hmn p) x q%:E s).
  move=>y [[hy _] hCone]; split=>//.
  have [hAngle _]:=(structure_projection_coneE hmn p x r%:E s y).1 hCone.
  apply/(structure_projection_coneE hmn p x q%:E s y); split=>//.
  rewrite lte_fin -inner_metric_distanceE.
  exact:le_lt_trans (hDiameter y x hy hx) haq.
have hBound:=le_trans (@measure_mono R _ phi hPhi _ _ hSubset) (hMass q hq).
apply:le_trans hBound _; rewrite lee_fin.
have hPowers:forall j,q^+j<=r^+j.
  elim=>[|j ih]; first by rewrite !expr0.
  rewrite !exprS; exact:ler_pM (ltW (andP hq).1) (exprn_ge0 _ (ltW (andP hq).1)) hqr ih.
have hPower:=hPowers m.
have hAlpha:0<=euclidean_unit_ball_volume R m:=ltW (@euclidean_unit_ball_volumeE R m).2.
have hCoeff:0<=lam*euclidean_unit_ball_volume R m:=mulr_ge0 (ltW hLam) hAlpha.
apply:ler_wpM2r; first by apply:exprn_ge0; exact:ltW hs.
apply:ler_wpM2l; [exact:hCoeff|exact:hPower].
Qed.
